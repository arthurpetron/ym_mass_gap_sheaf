/-
# Original signed bilinear, unchanged boundary observables, all odd extents

Full carrier support licenses the actual temporal ledger change of variables.
Both boundary observables return to their ORIGINAL heat-dressed polynomials;
the complete crossing interface becomes the actual spatial-link Gram product.
All signed coefficients, heat weights and overlapping link variables remain.

This proves the same-law identity at arbitrary odd extent. It does not yet
identify the assembled upper observable with the literal link reflection of
the lower observable at those extents. That pin, lower-channel locality, and
the established interface positivity are required for full slab positivity.
No consistency, time operator, vacuum stationarity, gap or limit is asserted.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages

namespace YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem support_zero (blocks : Nat) : SupportedQuaternionBlocks blocks polyZero :=
  fun _ h => False.elim (List.not_mem_nil h)

private theorem support_one (blocks : Nat) : SupportedQuaternionBlocks blocks polyOne := by
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  exact Nat.zero_le _

private theorem support_var {blocks i : Nat} (hi : i < 4 * blocks) : SupportedQuaternionBlocks blocks (polyVar i) := by
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  simp only [varMono, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

private theorem support_add {blocks : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q) :
    SupportedQuaternionBlocks blocks (polyAdd p q) := by
  intro t ht
  exact (List.mem_append.mp ht).elim (hp t) (hq t)

private theorem support_neg {blocks : Nat} {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_smul {blocks : Nat} (a : Q') {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polySmul a p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private structure QSupported (blocks : Nat) (q : PolyQuaternion) : Prop where
  scalar : SupportedQuaternionBlocks blocks q.scalar
  iPart : SupportedQuaternionBlocks blocks q.iPart
  jPart : SupportedQuaternionBlocks blocks q.jPart
  kPart : SupportedQuaternionBlocks blocks q.kPart

private theorem QSupported.conj {blocks : Nat} {q : PolyQuaternion} (h : QSupported blocks q) :
    QSupported blocks (PolyQuaternion.conj q) := ⟨h.scalar, support_neg h.iPart, support_neg h.jPart, support_neg h.kPart⟩

private theorem QSupported.mul {blocks : Nat} {p q : PolyQuaternion} (hp : QSupported blocks p) (hq : QSupported blocks q) :
    QSupported blocks (PolyQuaternion.mul p q) := by
  constructor <;> simp only [PolyQuaternion.mul]
  all_goals repeat' first
    | exact hp.scalar | exact hp.iPart | exact hp.jPart | exact hp.kPart
    | exact hq.scalar | exact hq.iPart | exact hq.jPart | exact hq.kPart
    | apply support_add | apply support_neg | apply supported_polyMul

private theorem link_support (extent : Nat) (link : Z4Link) :
    QSupported (boundaryCompleteSlabLinks extent).length (correctedSlabLinkPolynomial extent link) := by
  by_cases hl : link ∈ boundaryCompleteSlabLinks extent
  · rw [correctedSlabLinkPolynomial_of_mem hl]
    have hi := List.idxOf_lt_length_of_mem hl
    exact ⟨support_var (by omega), support_var (by omega), support_var (by omega), support_var (by omega)⟩
  · rw [correctedSlabLinkPolynomial_of_not_mem hl]
    exact ⟨support_one _, support_zero _, support_zero _, support_zero _⟩

private theorem temporal_link_support (extent half : Nat) (link : Z4Link) :
    QSupported (boundaryCompleteSlabLinks extent).length (upperTemporalLink extent half link) := by
  unfold upperTemporalLink
  split
  · exact (((link_support extent _).conj).mul (link_support extent link)).mul (link_support extent _)
  · exact link_support extent link

private theorem temporal_word_support (extent half : Nat) (face : Z4Plaq) :
    QSupported (boundaryCompleteSlabLinks extent).length (temporalFaceWord extent half face) :=
  (((temporal_link_support extent half _).mul (temporal_link_support extent half _)).mul
    (temporal_link_support extent half _).conj).mul (temporal_link_support extent half _).conj

private theorem character_support {blocks : Nat} {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    ∀ spin, SupportedQuaternionBlocks blocks (characterPolynomial p spin)
  | 0 => support_one _
  | 1 => support_smul 2 hp
  | n + 2 => support_add (supported_polyMul (support_smul 2 hp) (character_support hp (n + 1)))
      (support_smul (-1) (character_support hp n))

theorem temporal_character_support (extent half : Nat) (face : Z4Plaq) (spin : Nat) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length
      (characterPolynomial (temporalFaceWord extent half face).scalar spin) :=
  character_support (temporal_word_support extent half face).scalar spin

private theorem sum_support {A : Type} {blocks : Nat} (f : A → RatPoly)
    (hf : ∀ a, SupportedQuaternionBlocks blocks (f a)) :
    ∀ xs : List A, SupportedQuaternionBlocks blocks (finitePolySum f xs)
  | [] => support_zero _
  | a :: xs => support_add (hf a) (sum_support f hf xs)

private theorem fold_support {A : Type} {blocks : Nat} (f : A → RatPoly)
    (hf : ∀ a, SupportedQuaternionBlocks blocks (f a)) :
    ∀ xs : List A, SupportedQuaternionBlocks blocks (polynomialProduct f xs)
  | [] => support_one _
  | a :: xs => supported_polyMul (hf a) (fold_support f hf xs)

private theorem temporal_product_support (w : Q') (K half : Nat) (s : EdgeLabelling) (ids : List Nat) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length (temporalFaceProduct w K half s ids) :=
  fold_support _ (fun _ => support_smul _ (temporal_character_support _ _ _ _)) ids

theorem temporalObservableIntegrand_support (w : Q') (K half : Nat) (left right : EdgeLabelling → Q') :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length
      (temporalObservableIntegrand w K half left right) :=
  supported_polyMul (sum_support _ (fun _ => support_smul _ (temporal_product_support w K half _ _)) _)
    (supported_polyMul (fold_support _ (fun _ => sum_support _
      (fun _ => support_smul _ (temporal_character_support _ _ _ _)) _) _)
      (sum_support _ (fun _ => support_smul _ (temporal_product_support w K half _ _)) _))

theorem original_character_support (extent : Nat) (face : Z4Plaq) (spin : Nat) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length
      (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin) :=
  correctedSlabPlaquetteSpinFactor_support extent (fun _ => spin) face

private theorem weighted_support (w : Q') (K extent : Nat) (s : EdgeLabelling) (id : Nat) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length (weightedFacePolynomial w K extent s id) :=
  support_smul _ (original_character_support _ _ _)

theorem lowerObservable_support (w : Q') (K half : Nat) (c : EdgeLabelling → Q') :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length (lowerObservable w K half c) :=
  sum_support _ (fun _ => support_smul _ (fold_support _ (weighted_support w K (centralExtent half) _) _)) _

theorem upperObservable_support (w : Q') (K half : Nat) (c : EdgeLabelling → Q') :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length (upperObservable w K half c) :=
  sum_support _ (fun _ => support_smul _ (fold_support _ (weighted_support w K (centralExtent half) _) _)) _

theorem interfaceHeatProduct_support (w : Q') (K half : Nat) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length (interfaceHeatProduct w K half) :=
  fold_support _ (fun _ => sum_support _ (fun _ => support_smul _ (original_character_support _ _ _)) _) _

/-- Original product-Haar invariance and the fully supported independently
specified image, for the complete signed bilinear at every odd extent. -/
theorem exact_bilinear_eq_temporalHaar (w : Q') (K half : Nat) (left right : EdgeLabelling → Q') :
    finiteJointBilinear (centralHalfStates K half) left right (exactCorrectedSlabReflectedKernel w K half) ≈
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length (temporalObservableIntegrand w K half left right) := by
  have hp := supported_polyMul (lowerObservable_support w K half left)
    (supported_polyMul (interfaceHeatProduct_support w K half) (upperObservable_support w K half right))
  exact Q'.eqv_trans _ _ _ (exact_bilinear_eq_productHaar w K half left right)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (applyTemporalTranslationLedger_haar (centralExtent half) half _ hp))
      ((observableProduct_image w K half left right).haar
        (applyTemporalTranslationLedger_supported (centralExtent half) half _ hp)
        (temporalObservableIntegrand_support w K half left right)))

private theorem sum_row {A : Type} {blocks : Nat} (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → QuaternionHaarCarrierEqv blocks (f a) (g a)) →
      QuaternionHaarCarrierEqv blocks (finitePolySum f xs) (finitePolySum g xs)
  | [], _ => QuaternionHaarCarrierEqv.refl _ _
  | a :: xs, h => QuaternionHaarCarrierEqv.add (h a List.mem_cons_self)
      (sum_row f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem fold_row {A : Type} {blocks : Nat} (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → QuaternionHaarCarrierEqv blocks (f a) (g a)) →
      QuaternionHaarCarrierEqv blocks (polynomialProduct f xs) (polynomialProduct g xs)
  | [], _ => QuaternionHaarCarrierEqv.refl _ _
  | a :: xs, h => QuaternionHaarCarrierEqv.mul (h a List.mem_cons_self)
      (fold_row f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem temporalLower_haar_original (w : Q') (K half : Nat) (c : EdgeLabelling → Q') :
    QuaternionHaarCarrierEqv (boundaryCompleteSlabLinks (centralExtent half)).length
      (temporalLowerObservable w K half c) (lowerObservable w K half c) := by
  apply sum_row
  intro s _
  apply QuaternionHaarCarrierEqv.smul
  apply fold_row
  intro id hi
  apply QuaternionHaarCarrierEqv.smul
  exact RatPolyCoeffEqv.haarCarrier (characterPolynomial_coeffEqv
    (lower_face_unchanged (centralExtent half) half _ (mem_centralLowerFaceIds.mp hi).2).scalar _)

theorem temporalUpper_haar_original (w : Q') (K half : Nat) (c : EdgeLabelling → Q') :
    QuaternionHaarCarrierEqv (boundaryCompleteSlabLinks (centralExtent half)).length
      (temporalUpperObservable w K half c) (upperObservable w K half c) := by
  apply sum_row
  intro s _
  apply QuaternionHaarCarrierEqv.smul
  apply fold_row
  intro id hi
  apply QuaternionHaarCarrierEqv.smul
  exact upper_face_character (centralExtent half) half _ (mem_centralUpperFaceIds.mp hi).2 _

theorem haar_of_carrier {blocks : Nat} {p q : RatPoly} (h : QuaternionHaarCarrierEqv blocks p q) :
    quaternionHaar blocks p ≈ quaternionHaar blocks q :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff_eqv blocks (RatPolyCoeffEqv.one_mul p)))
    (Q'.eqv_trans _ _ _ (h polyOne) (haar_of_coeff_eqv blocks (RatPolyCoeffEqv.one_mul q)))

/-- SAME full original signed bilinear, unchanged original boundary
polynomials, and the actual spatial Gram interface, at every odd extent. -/
theorem exact_bilinear_eq_spatialGramHaar (w : Q') (K half : Nat) (left right : EdgeLabelling → Q') :
    finiteJointBilinear (centralHalfStates K half) left right (exactCorrectedSlabReflectedKernel w K half) ≈
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
        (polyMul (lowerObservable w K half left)
          (polyMul (interfacePolynomial w K half) (upperObservable w K half right))) :=
  Q'.eqv_trans _ _ _ (exact_bilinear_eq_temporalHaar w K half left right)
    (haar_of_carrier (QuaternionHaarCarrierEqv.mul (temporalLower_haar_original w K half left)
      (QuaternionHaarCarrierEqv.mul (temporalInterface_haar_gram w K half) (temporalUpper_haar_original w K half right))))

end YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm.temporal_character_support
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm.temporalObservableIntegrand_support
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm.original_character_support
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm.lowerObservable_support
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm.upperObservable_support
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm.interfaceHeatProduct_support
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm.exact_bilinear_eq_temporalHaar
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm.temporalLower_haar_original
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm.temporalUpper_haar_original
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm.haar_of_carrier
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm.exact_bilinear_eq_spatialGramHaar
