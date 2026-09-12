/-
# Same signed slab form after the temporal change of variables

The concrete original Haar-preserving ledger now acts on the full original
observable. The verified coefficient image and explicit support bounds give
the SAME signed bilinear/quadratic as its temporal-assignment Haar integral.
Facewise gauge cancellation then restores both original boundary observables
and removes the fixed-time links from every crossing heat factor.

The final expression retains F_left, the reduced interface, and the literal
reflection of F_right on the same 116 physical links. It is not yet a global
square decomposition or a reflection-positivity theorem. Physical transfer,
its gap, thermodynamic/continuum passage and Clay remain open.
-/

import YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages

namespace YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages
open YMGap.Continuum.BF4ExactSlabWeightedFaceFactorization
open YMGap.Continuum.BF4ExactSlabObservableHaarForm
open YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct
open YMGap.Continuum.BF4ExactSlabReflectedObservableHaarForm
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv
private abbrev Supported := SupportedQuaternionBlocks 116

private theorem slab_blocks : (boundaryCompleteSlabLinks 1).length = 116 := correctedSlabLinks_extent_one_length

private theorem support_zero : Supported polyZero := fun _ h => False.elim (List.not_mem_nil h)
private theorem support_one : Supported polyOne := by
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  exact Nat.zero_le _

private theorem support_var {i : Nat} (hi : i < 4 * 116) : Supported (polyVar i) := by
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  simp only [varMono, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

private theorem support_add {p q : RatPoly} (hp : Supported p) (hq : Supported q) : Supported (polyAdd p q) := by
  intro t ht
  exact (List.mem_append.mp ht).elim (hp t) (hq t)

private theorem support_neg {p : RatPoly} (hp : Supported p) : Supported (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_smul (a : Q') {p : RatPoly} (hp : Supported p) : Supported (polySmul a p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private structure QSupported (q : PolyQuaternion) : Prop where
  scalar : Supported q.scalar
  iPart : Supported q.iPart
  jPart : Supported q.jPart
  kPart : Supported q.kPart

private theorem QSupported.conj {q : PolyQuaternion} (h : QSupported q) : QSupported (PolyQuaternion.conj q) :=
  ⟨h.scalar, support_neg h.iPart, support_neg h.jPart, support_neg h.kPart⟩

private theorem QSupported.mul {p q : PolyQuaternion} (hp : QSupported p) (hq : QSupported q) :
    QSupported (PolyQuaternion.mul p q) := by
  constructor <;> simp only [PolyQuaternion.mul]
  all_goals repeat' first
    | exact hp.scalar | exact hp.iPart | exact hp.jPart | exact hp.kPart
    | exact hq.scalar | exact hq.iPart | exact hq.jPart | exact hq.kPart
    | apply support_add | apply support_neg | apply supported_polyMul

private theorem link_support (link : Z4Link) : QSupported (correctedSlabLinkPolynomial 1 link) := by
  by_cases hl : link ∈ boundaryCompleteSlabLinks 1
  · rw [correctedSlabLinkPolynomial_of_mem hl]
    have hi := List.idxOf_lt_length_of_mem hl
    rw [slab_blocks] at hi
    exact ⟨support_var (by omega), support_var (by omega), support_var (by omega), support_var (by omega)⟩
  · rw [correctedSlabLinkPolynomial_of_not_mem hl]
    exact ⟨support_one, support_zero, support_zero, support_zero⟩

private theorem temporal_link_support (link : Z4Link) : QSupported (upperTemporalLink 1 0 link) := by
  unfold upperTemporalLink
  split
  · exact (((link_support _).conj).mul (link_support link)).mul (link_support _)
  · exact link_support link

private theorem temporal_word_support (face : Z4Plaq) : QSupported (temporalFaceWord 1 0 face) :=
  (((temporal_link_support _).mul (temporal_link_support _)).mul
    (temporal_link_support _).conj).mul (temporal_link_support _).conj

private theorem character_support {p : RatPoly} (hp : Supported p) :
    ∀ spin, Supported (characterPolynomial p spin)
  | 0 => support_one
  | 1 => support_smul 2 hp
  | n + 2 => support_add (supported_polyMul (support_smul 2 hp) (character_support hp (n + 1)))
      (support_smul (-1) (character_support hp n))

private theorem temporal_character_support (face : Z4Plaq) (spin : Nat) : Supported (temporalCharacter 1 0 face spin) :=
  character_support (temporal_word_support face).scalar spin

private theorem sum_support {A : Type} (f : A → RatPoly) (hf : ∀ a, Supported (f a)) :
    ∀ xs : List A, Supported (finitePolySum f xs)
  | [] => support_zero
  | a :: xs => support_add (hf a) (sum_support f hf xs)

private theorem fold_support {A : Type} (f : A → RatPoly) (hf : ∀ a, Supported (f a)) :
    ∀ xs : List A, Supported (xs.foldr (fun a p => polyMul (f a) p) polyOne)
  | [] => support_one
  | a :: xs => supported_polyMul (hf a) (fold_support f hf xs)

private theorem temporal_product_support (w : Q') (K : Nat) (state : EdgeLabelling) (ids : List Nat) :
    Supported (temporalFaceProduct w K state ids) :=
  fold_support _ (fun id => support_smul _ (temporal_character_support _ (state id))) ids

private theorem temporal_lower_support (w : Q') (K : Nat) (c : EdgeLabelling → Q') :
    Supported (temporalLowerObservable w K c) :=
  sum_support _ (fun state => support_smul _ (temporal_product_support w K state _)) _

private theorem temporal_upper_support (w : Q') (K : Nat) (c : EdgeLabelling → Q') :
    Supported (temporalUpperObservable w K c) :=
  sum_support _ (fun _ => support_smul _ (temporal_product_support w K _ _)) _

private theorem temporal_interface_support (w : Q') (K : Nat) : Supported (temporalInterfaceHeatProduct w K) :=
  fold_support _ (fun _ => sum_support _ (fun spin => support_smul _ (temporal_character_support _ spin)) _) _

theorem temporalObservableIntegrand_support (w : Q') (K : Nat) (left right : EdgeLabelling → Q') :
    SupportedQuaternionBlocks 116 (temporalObservableIntegrand w K left right) :=
  supported_polyMul (temporal_lower_support w K left)
    (supported_polyMul (temporal_interface_support w K) (temporal_upper_support w K right))

private theorem original_weighted_support (w : Q') (K : Nat) (state : EdgeLabelling) (id : Nat) :
    Supported (weightedFacePolynomial w K state id) := by
  have h := correctedSlabPlaquetteSpinFactor_support 1 (fun _ => state id) (slabPlaquetteAt 1 id)
  rw [slab_blocks] at h
  exact support_smul _ h

private theorem original_upper_support (w : Q') (K : Nat) (c : EdgeLabelling → Q') :
    Supported (upperObservable w K c) := by
  apply sum_support
  intro state
  apply support_smul
  rw [upperPolynomial_eq_fold]
  exact fold_support _ (original_weighted_support w K _) _

/-- The SAME signed bilinear, with the complete original observable and
heat coefficients, after the concrete Haar-preserving change of variables. -/
theorem exact_bilinear_eq_temporalHaar (w : Q') (K : Nat) (left right : EdgeLabelling → Q') :
    finiteJointBilinear (centralHalfStates K 0) left right (exactCorrectedSlabReflectedKernel w K 0) ≈
      quaternionHaar 116 (temporalObservableIntegrand w K left right) := by
  let p := polyMul (lowerObservable w K left) (polyMul (interfaceHeatProduct w K) (upperObservable w K right))
  have hp : Supported p := supported_polyMul (lowerObservable_support w K left)
    (supported_polyMul (interfaceHeatProduct_support w K) (original_upper_support w K right))
  have hs := applyTemporalTranslationLedger_supported 1 0 p
  have hh := applyTemporalTranslationLedger_haar 1 0 p
  rw [slab_blocks] at hs hh
  exact Q'.eqv_trans _ _ _ (exact_bilinear_eq_productHaar w K left right)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (hh hp))
      ((observableProduct_image w K left right).haar (hs hp) (temporalObservableIntegrand_support w K left right)))

theorem exact_quadratic_eq_temporalHaar (w : Q') (K : Nat) (c : EdgeLabelling → Q') :
    exactSlabAllCutoffQuadratic w K c ≈ quaternionHaar 116 (temporalObservableIntegrand w K c c) :=
  exact_bilinear_eq_temporalHaar w K c c

private theorem sum_row {A : Type} (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → HaarCarrierEqv 116 (f a) (g a)) →
      HaarCarrierEqv 116 (finitePolySum f xs) (finitePolySum g xs)
  | [], _ => HaarCarrierEqv.refl _ _
  | a :: xs, h => HaarCarrierEqv.add (h a List.mem_cons_self)
      (sum_row f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem fold_row {A : Type} (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → HaarCarrierEqv 116 (f a) (g a)) →
      HaarCarrierEqv 116 (xs.foldr (fun a p => polyMul (f a) p) polyOne)
        (xs.foldr (fun a p => polyMul (g a) p) polyOne)
  | [], _ => HaarCarrierEqv.refl _ _
  | a :: xs, h => HaarCarrierEqv.mul (h a List.mem_cons_self)
      (fold_row f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem temporalLowerObservable_haar_original (w : Q') (K : Nat) (c : EdgeLabelling → Q') :
    HaarCarrierEqv 116 (temporalLowerObservable w K c) (lowerObservable w K c) := by
  apply sum_row
  intro state _
  apply HaarCarrierEqv.smul
  rw [lowerPolynomial_eq_fold]
  apply fold_row
  intro id hi
  apply HaarCarrierEqv.smul
  exact RatPolyCoeffEqv.haarCarrier (characterPolynomial_coeffEqv
    (lower_face_unchanged 1 0 (slabPlaquetteAt 1 id) (mem_centralLowerFaceIds.mp hi).2).scalar _)

theorem temporalUpperObservable_haar_original (w : Q') (K : Nat) (c : EdgeLabelling → Q') :
    HaarCarrierEqv 116 (temporalUpperObservable w K c) (upperObservable w K c) := by
  apply sum_row
  intro state _
  apply HaarCarrierEqv.smul
  rw [upperPolynomial_eq_fold]
  apply fold_row
  intro id hi
  apply HaarCarrierEqv.smul
  have h := upper_face_character 1 0 (slabPlaquetteAt 1 id) (mem_centralUpperFaceIds.mp hi).2
  rw [slab_blocks] at h
  exact h _

/-- The remaining crossing character uses the original lower link and its
actual upper reflected mate, with no fixed-time factor. -/
def reducedFaceCharacter (face : Z4Plaq) (spin : Nat) : RatPoly :=
  characterPolynomial (PolyQuaternion.mul (correctedSlabLinkPolynomial 1 (faceLinkA face))
    (PolyQuaternion.conj (correctedSlabLinkPolynomial 1 (faceLinkC face)))).scalar spin

def reducedFaceHeatPolynomial (w : Q') (K id : Nat) : RatPoly :=
  finitePolySum (fun spin => polySmul (coeffAt (heatKernelPacket K w) spin)
    (reducedFaceCharacter (slabPlaquetteAt 1 id) spin)) (List.range (K + 1))

def reducedInterfaceHeatProduct (w : Q') (K : Nat) : RatPoly :=
  (centralFixedFaceIds 0).foldr (fun id p => polyMul (reducedFaceHeatPolynomial w K id) p) polyOne

theorem temporalInterfaceHeatProduct_haar_reduced (w : Q') (K : Nat) :
    HaarCarrierEqv 116 (temporalInterfaceHeatProduct w K) (reducedInterfaceHeatProduct w K) := by
  apply fold_row
  intro id hi
  apply sum_row
  intro spin _
  apply HaarCarrierEqv.smul
  have h := crossing_face_character 1 0 (slabPlaquetteAt 1 id) (mem_centralFixedFaceIds.mp hi).2 spin
  rw [slab_blocks] at h
  exact h

theorem reducedInterfaceHeatProduct_support (w : Q') (K : Nat) :
    SupportedQuaternionBlocks 116 (reducedInterfaceHeatProduct w K) :=
  fold_support _ (fun _ => sum_support _ (fun spin => support_smul _
    (character_support ((link_support _).mul (link_support _).conj).scalar spin)) _) _

private theorem haar_row_value {p q : RatPoly} (h : HaarCarrierEqv 116 p q) :
    quaternionHaar 116 p ≈ quaternionHaar 116 q := by
  have one_left (r : RatPoly) : quaternionHaar 116 (polyMul polyOne r) ≈ quaternionHaar 116 r :=
    Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_comm 116 _ _) (quaternionHaar_polyMul_one_right 116 r)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (one_left p)) (Q'.eqv_trans _ _ _ (h polyOne) (one_left q))

/-- ORIGINAL signed bilinear, unchanged lower observable and literal
reflection, with every fixed-time crossing factor removed by the proved
change of variables. Global reflected-square gluing is still required. -/
theorem exact_bilinear_eq_reducedReflectedHaar (w : Q') (K : Nat) (left right : EdgeLabelling → Q') :
    finiteJointBilinear (centralHalfStates K 0) left right (exactCorrectedSlabReflectedKernel w K 0) ≈
      quaternionHaar 116 (polyMul (lowerObservable w K left)
        (polyMul (reducedInterfaceHeatProduct w K)
          (reflectCorrectedSlabPolynomial 1 (lowerObservable w K right)))) := by
  have hrow := HaarCarrierEqv.mul (temporalLowerObservable_haar_original w K left)
    (HaarCarrierEqv.mul (temporalInterfaceHeatProduct_haar_reduced w K) (temporalUpperObservable_haar_original w K right))
  refine Q'.eqv_trans _ _ _ (exact_bilinear_eq_temporalHaar w K left right) ?_
  refine Q'.eqv_trans _ _ _ (haar_row_value hrow) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polyMul_assoc 116 _ _ _)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (lowerObservable_reflection_insert w K right _
    (supported_polyMul (lowerObservable_support w K left) (reducedInterfaceHeatProduct_support w K)))) ?_
  exact quaternionHaar_polyMul_assoc 116 _ _ _

theorem exact_quadratic_eq_reducedReflectedHaar (w : Q') (K : Nat) (c : EdgeLabelling → Q') :
    exactSlabAllCutoffQuadratic w K c ≈
      quaternionHaar 116 (polyMul (lowerObservable w K c)
        (polyMul (reducedInterfaceHeatProduct w K) (reflectCorrectedSlabPolynomial 1 (lowerObservable w K c)))) :=
  exact_bilinear_eq_reducedReflectedHaar w K c c

/-- Actual reflected spatial-link Gram kernels, with the original heat
coefficients. No fixed-time link occurs in either Gram argument. -/
def spatialGramFaceHeatPolynomial (w : Q') (K id : Nat) : RatPoly :=
  finitePolySum (fun spin => polySmul (coeffAt (heatKernelPacket K w) spin)
    (reflectedSpatialLinkGram 1 (faceLinkA (slabPlaquetteAt 1 id)) spin).1) (List.range (K + 1))

def spatialGramInterface (w : Q') (K : Nat) : RatPoly :=
  (centralFixedFaceIds 0).foldr (fun id p => polyMul (spatialGramFaceHeatPolynomial w K id) p) polyOne

theorem reducedInterfaceHeatProduct_haar_spatialGram (w : Q') (K : Nat) :
    HaarCarrierEqv 116 (reducedInterfaceHeatProduct w K) (spatialGramInterface w K) := by
  apply fold_row
  intro id hi
  apply sum_row
  intro spin _
  apply HaarCarrierEqv.smul
  have hf := (mem_centralFixedFaceIds.mp hi).2
  have hc := crossing_face_character 1 0 (slabPlaquetteAt 1 id) hf spin
  have hg := (crossing_face_reflected_gram 0 (slabPlaquetteAt 1 id) hf spin).1
  change HaarCarrierEqv (boundaryCompleteSlabLinks 1).length _ _ at hg
  rw [slab_blocks] at hc hg
  exact HaarCarrierEqv.trans (HaarCarrierEqv.symm hc) hg

/-- SAME original bilinear on its unchanged reflected observables, with
the interface expressed entirely in literal reflected SPATIAL-link Gram
kernels. This is the input to global reflected-square gluing, not its proof. -/
theorem exact_bilinear_eq_spatialGramHaar (w : Q') (K : Nat) (left right : EdgeLabelling → Q') :
    finiteJointBilinear (centralHalfStates K 0) left right (exactCorrectedSlabReflectedKernel w K 0) ≈
      quaternionHaar 116 (polyMul (lowerObservable w K left)
        (polyMul (spatialGramInterface w K)
          (reflectCorrectedSlabPolynomial 1 (lowerObservable w K right)))) :=
  Q'.eqv_trans _ _ _ (exact_bilinear_eq_reducedReflectedHaar w K left right)
    (haar_row_value (HaarCarrierEqv.mul (HaarCarrierEqv.refl 116 _)
      (HaarCarrierEqv.mul (reducedInterfaceHeatProduct_haar_spatialGram w K) (HaarCarrierEqv.refl 116 _))))

theorem exact_quadratic_eq_spatialGramHaar (w : Q') (K : Nat) (c : EdgeLabelling → Q') :
    exactSlabAllCutoffQuadratic w K c ≈
      quaternionHaar 116 (polyMul (lowerObservable w K c)
        (polyMul (spatialGramInterface w K) (reflectCorrectedSlabPolynomial 1 (lowerObservable w K c)))) :=
  exact_bilinear_eq_spatialGramHaar w K c c

end YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm

#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm.temporalObservableIntegrand_support
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm.exact_bilinear_eq_temporalHaar
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm.exact_quadratic_eq_temporalHaar
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm.temporalLowerObservable_haar_original
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm.temporalUpperObservable_haar_original
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm.reducedFaceCharacter
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm.reducedFaceHeatPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm.reducedInterfaceHeatProduct
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm.temporalInterfaceHeatProduct_haar_reduced
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm.reducedInterfaceHeatProduct_support
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm.exact_bilinear_eq_reducedReflectedHaar
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm.exact_quadratic_eq_reducedReflectedHaar
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm.spatialGramFaceHeatPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm.spatialGramInterface
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm.reducedInterfaceHeatProduct_haar_spatialGram
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm.exact_bilinear_eq_spatialGramHaar
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm.exact_quadratic_eq_spatialGramHaar
