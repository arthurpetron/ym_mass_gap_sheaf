/-
# Literal translation of signed scheduled probes and reflected chart insertions

Every character coefficient, factor repetition, schedule order and outer
signed coefficient is retained. The computed arbitrary-extent Haar placement
transports the original ordered plaquette words; spatial translation of the
schedule and translation of its placement time describe the literal target
probe, not a replacement coordinate observable.

For aligned boxes, spatial shift d and time shift 2*d send the complete
reflected insertion at recentering margin r to the one at margin r+d.
The common radius, physical distance labels and any eventual heat cutoff
are unchanged. This polynomial pin makes no comparison with the additional
target action factors and proves no spatial decay or limiting-state equality.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes
import YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedProbe

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe (placeProbes)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (placedSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive (mirrorSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm (Span Within Physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding (Placement)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry (adjacentEvenExtent)

local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private theorem imageSum {A : Type} {source target : Nat} (E : BlockEmbedding source target)
    (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → QuaternionPrefixPolynomialEqv target (E.polynomial (f a)) (g a)) →
    QuaternionPrefixPolynomialEqv target (E.polynomial (finitePolySum f xs)) (finitePolySum g xs)
  | [], _ => .nil
  | a::xs, h => by
      change QuaternionPrefixPolynomialEqv target (E.polynomial (polyAdd _ _)) _
      rw [E.polynomial_add]
      exact (h a List.mem_cons_self).append
        (imageSum E f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem imageProduct {A : Type} {source target : Nat} (E : BlockEmbedding source target)
    (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → QuaternionPrefixPolynomialEqv target (E.polynomial (f a)) (g a)) →
    QuaternionPrefixPolynomialEqv target (E.polynomial (polynomialProduct f xs)) (polynomialProduct g xs)
  | [], _ => E.polynomial_one_prefix
  | a::xs, h => by
      change QuaternionPrefixPolynomialEqv target (E.polynomial (polyMul _ _)) _
      rw [E.polynomial_mul]
      exact (h a List.mem_cons_self).mul
        (imageProduct E f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem factor_pin (P : Placement) (f : FaceFactor)
    (hf : f.1 ∈ boundaryCompleteSlabPlaquettes P.source) :
    QuaternionPrefixPolynomialEqv (B P.target)
      (P.embedding.polynomial (factor
        (fun face spin => characterPolynomial (correctedSlabPlaquettePolynomial P.source face).scalar spin) f))
      (factor
        (fun face spin => characterPolynomial (correctedSlabPlaquettePolynomial P.target face).scalar spin)
        (shiftFace P.space P.time f.1, f.2)) := by
  apply imageSum
  intro term _
  rw [BlockEmbedding.polynomial_smul]
  exact (P.character_pin hf term.1).smul term.2

private theorem product_pin (P : Placement) (fs : List FaceFactor)
    (hf : ∀ f, f ∈ fs → f.1 ∈ boundaryCompleteSlabPlaquettes P.source) :
    QuaternionPrefixPolynomialEqv (B P.target)
      (P.embedding.polynomial (sweptProduct P.source 0 fs))
      (sweptProduct P.target 0 (fs.map (fun f => (shiftFace P.space P.time f.1, f.2)))) := by
  rw [swept_zero, swept_zero]
  simpa only [product, polynomialProduct, List.foldr_map] using
    (imageProduct P.embedding
      (factor (fun face spin =>
        characterPolynomial (correctedSlabPlaquettePolynomial P.source face).scalar spin))
      (fun f => factor (fun face spin =>
        characterPolynomial (correctedSlabPlaquettePolynomial P.target face).scalar spin)
        (shiftFace P.space P.time f.1, f.2)) fs (fun f h => factor_pin P f (hf f h)))

private theorem shiftFace_timeShift (space time start : Nat) (face : Z4Plaq) :
    shiftFace space time (timeShiftPlaquette start face) =
      timeShiftPlaquette (start+time) (shiftFace space 0 face) := by
  obtain ⟨⟨a,b,c,z⟩, plane⟩ := face
  simp only [shiftFace, shiftVertex, timeShiftPlaquette, timeShiftVertex, Nat.add_zero, Nat.add_assoc]

private theorem placeProbes_translation (space time start : Nat) (fs : List FaceFactor) :
    placeProbes (start+time) (fs.map (translateFactor space)) =
      (placeProbes start fs).map (fun f => (shiftFace space time f.1, f.2)) := by
  simp only [placeProbes, List.map_map, Function.comp_def, translateFactor,
    shiftFace_timeShift]

/-- Exact flattening identity: only the spatial face and ambient time are translated. -/
theorem placeWindowProbes_translation (space time start : Nat)
    (fs : List (Nat × List FaceFactor)) :
    placeWindowProbes (start+time) (translateSchedule space fs) =
      (placeWindowProbes start fs).map (fun f => (shiftFace space time f.1, f.2)) := by
  simp only [placeWindowProbes, translateSchedule, List.flatMap_map, List.map_flatMap]
  apply congrArg (fun f => fs.flatMap f)
  funext e
  have ht : start+time+e.1 = (start+e.1)+time := by omega
  rw [ht]
  exact placeProbes_translation space time (start+e.1) e.2

/-- Literal placed-span transport. The only guard is physicality of each
actual source face after placement; all signs and all list orders survive. -/
theorem placedSpan_pin (P : Placement) (start : Nat) : ∀ xs : Span,
    (∀ x, x ∈ xs → ∀ f, f ∈ placeWindowProbes start x.2 →
      f.1 ∈ boundaryCompleteSlabPlaquettes P.source) →
    QuaternionPrefixPolynomialEqv (B P.target)
      (P.embedding.polynomial (placedSpan P.source start xs))
      (placedSpan P.target (start+P.time) (translateSpan P.space xs))
  | [], _ => .nil
  | x::xs, hf => by
      change QuaternionPrefixPolynomialEqv (B P.target)
        (P.embedding.polynomial (polyAdd
          (polySmul x.1 (sweptProduct P.source 0 (placeWindowProbes start x.2)))
          (placedSpan P.source start xs)))
        (polyAdd
          (polySmul x.1 (sweptProduct P.target 0
            (placeWindowProbes (start+P.time) (translateSchedule P.space x.2))))
          (placedSpan P.target (start+P.time) (translateSpan P.space xs)))
      rw [BlockEmbedding.polynomial_add, BlockEmbedding.polynomial_smul,
        placeWindowProbes_translation]
      exact ((product_pin P _ (hf x List.mem_cons_self)).smul x.1).append
        (placedSpan_pin P start xs (fun y hy => hf y (List.mem_cons_of_mem x hy)))

/-- Spatial shifts add without changing any distance label or coefficient. -/
theorem translateSpan_comp (r s : Nat) (xs : DistanceSpan) :
    translateSpan s (translateSpan r xs) = translateSpan (r+s) xs := by
  simp only [translateSpan, translateSchedule, translateFactor, List.map_map,
    Function.comp_def, shiftFace_comp, Nat.zero_add]
  rfl

theorem encodeChart_translate (shift H : Nat) (xs : DistanceSpan) :
    encodeChart H (translateSpan shift xs) = translateSpan shift (encodeChart H xs) := by
  simp only [encodeChart, encodeSchedule, translateSpan, translateSchedule,
    List.map_map, Function.comp_def]

theorem mirrorSpan_translate (shift H : Nat) (xs : Span) :
    mirrorSpan H (translateSpan shift xs) = translateSpan shift (mirrorSpan H xs) := by
  simp only [mirrorSpan, mirrorSchedule, translateSpan, translateSchedule,
    List.map_map, Function.comp_def]

private theorem translate_within {L : Nat} (shift : Nat) (xs : Span)
    (hx : Within L xs) : Within L (translateSpan shift xs) := by
  intro x hm e he
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  exact hx y hy f hf

/-- The aligned ambient placement carries the full literal recentered span,
with its entire schedule at unchanged offsets inside the same chart window. -/
theorem aligned_span_pin (base r d H t : Nat) (xs : Span)
    (hx : Physical base xs) (hwithin : Within (2*H) xs) :
    QuaternionPrefixPolynomialEqv (B (chartExtent base (r+d) H t))
      ((placement base r d H t).embedding.polynomial
        (placedSpan (chartExtent base r H t) (paddedWidth base r+1+t)
          (translateSpan (r+1) xs)))
      (placedSpan (chartExtent base (r+d) H t) (paddedWidth base (r+d)+1+t)
        (translateSpan (r+d+1) xs)) := by
  have hw : paddedWidth base r ≤ chartExtent base r H t := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have ht : (paddedWidth base r+1+t)+2*H ≤ chartExtent base r H t := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have hphysical : Physical (paddedWidth base r) (translateSpan (r+1) xs) :=
    translateSpan_physical (by unfold paddedWidth; omega) xs hx
  have htranslated := placedSpan_pin (placement base r d H t)
    (paddedWidth base r+1+t) (translateSpan (r+1) xs)
    (fun x hm => placeWindowProbes_physical hw ht x.2
      (translate_within (r+1) xs hwithin x hm) (hphysical x hm))
  change QuaternionPrefixPolynomialEqv (B (chartExtent base (r+d) H t))
    ((placement base r d H t).embedding.polynomial
      (placedSpan (chartExtent base r H t) (paddedWidth base r+1+t)
        (translateSpan (r+1) xs)))
    (placedSpan (chartExtent base (r+d) H t) ((paddedWidth base r+1+t)+2*d)
      (translateSpan d (translateSpan (r+1) xs))) at htranslated
  have hstart : (paddedWidth base r+1+t)+2*d = paddedWidth base (r+d)+1+t := by
    have h := chart_start_shift base r d
    omega
  have hshift : r+1+d = r+d+1 := by omega
  simpa only [hstart, translateSpan_comp, hshift] using htranslated

private theorem mirror_within (H : Nat) (xs : Span) : Within (2*H) (mirrorSpan H xs) := by
  intro x hm
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hm
  exact mirrorSchedule_within H y.2

private theorem mirror_physical {width : Nat} (H : Nat) (xs : Span)
    (hx : Physical width xs) : Physical width (mirrorSpan H xs) := by
  intro x hm
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
  exact mirrorSchedule_faces H y.2 (hx y hy)

/-- Prefix pin for the literal two-factor insertion of the existing chartScalar.
Both physical spans use the same H, and the heat-cutoff stage is not changed. -/
theorem aligned_chartInsertion_pin (base r d H t : Nat) (x y : PhysicalSpan base)
    (_hx : radius x.val ≤ H) (hy : radius y.val ≤ H) :
    QuaternionPrefixPolynomialEqv (B (chartExtent base (r+d) H t))
      ((placement base r d H t).embedding.polynomial
        (polyMul
          (placedSpan (chartExtent base r H t) (paddedWidth base r+1+t)
            (mirrorSpan H (encodeChart H (recenter r x).val)))
          (placedSpan (chartExtent base r H t) (paddedWidth base r+1+t)
            (encodeChart H (recenter r y).val))))
      (polyMul
        (placedSpan (chartExtent base (r+d) H t) (paddedWidth base (r+d)+1+t)
          (mirrorSpan H (encodeChart H (recenter (r+d) x).val)))
        (placedSpan (chartExtent base (r+d) H t) (paddedWidth base (r+d)+1+t)
          (encodeChart H (recenter (r+d) y).val))) := by
  have hxphysical := encodeChart_physical H x.val x.property
  have hyphysical := encodeChart_physical H y.val y.property
  have hywithin : Within (2*H) (encodeChart H y.val) := by
    intro a ha e he
    have h := encodeChart_within H y.val hy a ha e he
    omega
  have hleft := aligned_span_pin base r d H t (mirrorSpan H (encodeChart H x.val))
    (mirror_physical H _ hxphysical) (mirror_within H _)
  have hright := aligned_span_pin base r d H t (encodeChart H y.val) hyphysical hywithin
  rw [BlockEmbedding.polynomial_mul]
  simpa only [recenter, encodeChart_translate, mirrorSpan_translate] using hleft.mul hright

end YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedProbe

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedProbe.placeWindowProbes_translation
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedProbe.placedSpan_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedProbe.translateSpan_comp
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedProbe.encodeChart_translate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedProbe.mirrorSpan_translate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedProbe.aligned_span_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedProbe.aligned_chartInsertion_pin
