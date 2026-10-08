/-
# Literal closed Wilson words under the ORIGINAL auxiliary vertex ledger

The actual all-link ledger sends every physical oriented link to its common
endpoint-gauged image. Compatibility and closedness cancel those gauges in
the sphere/Haar ideal. The existing `Invariant` predicate retains all three
auxiliary coordinates and arbitrary supported spectator insertions.

This finite observable law supplies no infinitesimal Gauss generator,
simultaneous-endpoint signed-response estimate, or continuum/gap conclusion.
-/

import YMGap.Continuum.BF4ExactSlabVertexGaugeAction
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow

namespace YMGap.Continuum.BF4ExactSlabVertexGaugeWilsonWord

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge
open YMGap.Continuum.BF4ExactSlabVertexGaugeAction
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing
open YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage
open YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate

private abbrev Lift (p : RatPoly) := liftBoundary 3 p
private abbrev Steps (extent : Nat) (tags : Z4Vertex → Option (Fin 3)) :=
  gaugeLedger (startTag extent tags) (finishTag extent tags)

private def liftedEntry (extent : Nat) (e : OrientedBF4Link) : PolyQuaternion :=
  liftThree (orientedCorrectedSlabLinkPolynomial extent e)

private def vertexEntry (extent : Nat) (tags : Z4Vertex → Option (Fin 3))
    (e : OrientedBF4Link) : PolyQuaternion :=
  if e.reverse then PolyQuaternion.conj (vertexLink extent tags e.link)
  else vertexLink extent tags e.link

private def pathData (extent : Nat) (edges : List OrientedBF4Link) :
    List (PolyQuaternion × Z4Vertex) :=
  edges.map (fun e => (liftedEntry extent e, entryFinish e))

private theorem path_finish (extent : Nat) (start : Z4Vertex) :
    ∀ edges : List OrientedBF4Link,
      SU2QuaternionHaarGaugeWord.finish start (pathData extent edges) = pathFinish start edges
  | [] => rfl
  | e :: es => path_finish extent (entryFinish e) es

private theorem lifted_word (extent : Nat) : ∀ edges : List OrientedBF4Link,
    PaddedQuaternionCoeffEqv (linkCount extent+3) (liftThree (word extent edges))
      (SU2QuaternionHaarGaugeWord.word (pathData extent edges))
  | [] => ⟨lift_one _ 3, RatPolyCoeffEqv.refl _, RatPolyCoeffEqv.refl _, RatPolyCoeffEqv.refl _⟩
  | e :: es => by
      change PaddedQuaternionCoeffEqv _
        (liftThree (PolyQuaternion.mul (orientedCorrectedSlabLinkPolynomial extent e) (word extent es))) _
      simp only [liftThree, lift_mul]
      exact (PaddedQuaternionCoeffEqv.refl _ _).mul (lifted_word extent es)

private theorem ledger_entry (extent : Nat) (tags : Z4Vertex → Option (Fin 3))
    (e : OrientedBF4Link) (he : e.link ∈ boundaryCompleteSlabLinks extent) :
    PaddedQuaternionCoeffEqv (linkCount extent+3)
      (slabGaugeQuaternion extent tags (liftedEntry extent e)) (vertexEntry extent tags e) := by
  have h := slabGauge_link tags he
  unfold liftedEntry vertexEntry orientedCorrectedSlabLinkPolynomial
  cases hr : e.reverse
  · simpa only [hr, if_false] using h
  · simp only [if_true, liftThree, lift_conj]
    exact (applySteps_conj (by omega : 0 < linkCount extent+2)
      (Steps extent tags) (liftedLink extent e.link)).trans h.conj

private theorem ledger_word (extent : Nat) (tags : Z4Vertex → Option (Fin 3)) :
    ∀ edges : List OrientedBF4Link,
      (∀ e, e ∈ edges → e.link ∈ boundaryCompleteSlabLinks extent) →
      PaddedQuaternionCoeffEqv (linkCount extent+3)
        (slabGaugeQuaternion extent tags (liftThree (word extent edges)))
        (wordWith (vertexEntry extent tags) edges)
  | [], _ => by
      have h : PaddedQuaternionCoeffEqv (linkCount extent+3)
          (liftThree PolyQuaternion.one) PolyQuaternion.one :=
        ⟨lift_one _ 3, RatPolyCoeffEqv.refl _, RatPolyCoeffEqv.refl _, RatPolyCoeffEqv.refl _⟩
      exact (h.applySteps (by omega : 0 < linkCount extent+2) (Steps extent tags)).trans
        (applySteps_one (by omega : 0 < linkCount extent+2) (Steps extent tags))
  | e :: es, hp => by
      change PaddedQuaternionCoeffEqv _
        (slabGaugeQuaternion extent tags (liftThree
          (PolyQuaternion.mul (orientedCorrectedSlabLinkPolynomial extent e) (word extent es)))) _
      simp only [liftThree, lift_mul]
      exact (applySteps_mul (by omega : 0 < linkCount extent+2) (Steps extent tags)
        (liftedEntry extent e) (liftThree (word extent es))).trans
        ((ledger_entry extent tags e (hp e List.mem_cons_self)).mul
          (ledger_word extent tags es (fun f hf => hp f (List.mem_cons_of_mem e hf))))

private theorem vertex_entry (extent : Nat) (tags : Z4Vertex → Option (Fin 3))
    (e : OrientedBF4Link) :
    PolyQuaternionCoeffEqv (vertexEntry extent tags e)
      (gaugeLink (auxiliaryGauge (tags (entryStart e))) (liftedEntry extent e)
        (auxiliaryGauge (tags (entryFinish e)))) := by
  unfold vertexEntry vertexLink liftedEntry entryStart entryFinish orientedCorrectedSlabLinkPolynomial
  cases hr : e.reverse
  · exact PolyQuaternionCoeffEqv.refl _
  · simpa only [hr, if_true, liftThree, lift_conj] using
      gaugeLink_conj (auxiliaryGauge (tags e.link.1)) (liftedLink extent e.link)
        (auxiliaryGauge (tags (addE e.link.1 e.link.2)))

private theorem vertex_word (extent : Nat) (tags : Z4Vertex → Option (Fin 3))
    (start : Z4Vertex) : ∀ edges : List OrientedBF4Link, Compatible start edges →
    PolyQuaternionCoeffEqv (wordWith (vertexEntry extent tags) edges)
      (SU2QuaternionHaarGaugeWord.gaugeWord (fun v => auxiliaryGauge (tags v)) start
        (pathData extent edges))
  | [], _ => .refl _
  | e :: es, hc => by
      have he := vertex_entry extent tags e
      rw [hc.1] at he
      exact he.mul (vertex_word extent tags (entryFinish e) es hc.2)

private theorem auxiliary_support (extent : Nat) (tag : Option (Fin 3)) :
    QuaternionSupported (linkCount extent+3) (auxiliaryGauge tag) := by
  cases tag with
  | none => exact ⟨supported_one _, fun _ h => False.elim (List.not_mem_nil h),
      fun _ h => False.elim (List.not_mem_nil h), fun _ h => False.elim (List.not_mem_nil h)⟩
  | some j => exact .coordinate (by have := j.isLt; omega)

private theorem vertex_word_support (extent : Nat) (tags : Z4Vertex → Option (Fin 3)) :
    ∀ edges : List OrientedBF4Link,
      QuaternionSupported (linkCount extent+3) (wordWith (vertexEntry extent tags) edges)
  | [] => ⟨supported_one _, fun _ h => False.elim (List.not_mem_nil h),
      fun _ h => False.elim (List.not_mem_nil h), fun _ h => False.elim (List.not_mem_nil h)⟩
  | e :: es => by
      have h := ((auxiliary_support extent (tags e.link.1)).conj.mul
        (lifted_link_support extent e.link)).mul
          (auxiliary_support extent (tags (addE e.link.1 e.link.2)))
      have he : QuaternionSupported (linkCount extent+3) (vertexEntry extent tags e) := by
        unfold vertexEntry
        split
        · exact h.conj
        · exact h
      exact he.mul (vertex_word_support extent tags es)

private theorem path_word_support (extent : Nat) : ∀ edges : List OrientedBF4Link,
    QuaternionSupported (linkCount extent+3)
      (SU2QuaternionHaarGaugeWord.word (pathData extent edges))
  | [] => ⟨supported_one _, fun _ h => False.elim (List.not_mem_nil h),
      fun _ h => False.elim (List.not_mem_nil h), fun _ h => False.elim (List.not_mem_nil h)⟩
  | e :: es => by
      have h := oriented_supported extent e
      have he : QuaternionSupported (linkCount extent+3) (liftedEntry extent e) :=
        ⟨lift_supported h.scalar 3, lift_supported h.iPart 3,
          lift_supported h.jPart 3, lift_supported h.kPart 3⟩
      exact he.mul (path_word_support extent es)

/-- Every literal closed physical word under the SAME all-link vertex ledger.
The ordered occurrences, inverse orientations and three auxiliary blocks remain. -/
theorem closedWord_invariant (extent : Nat) (tags : Z4Vertex → Option (Fin 3))
    (start : Z4Vertex) (edges : List OrientedBF4Link) (hc : Compatible start edges)
    (hclosed : pathFinish start edges = start)
    (hp : ∀ e, e ∈ edges → e.link ∈ boundaryCompleteSlabLinks extent) (spin : Nat) :
    Invariant extent tags (character extent edges spin) := by
  have hs := character_supported extent edges spin
  have hl := lift_supported hs 3
  have hg := gaugePolynomial_supported (startTag extent tags) (finishTag extent tags) _ hl
  have hv := SU2QuaternionRelativeHeatPairGeometry.character_supported
    (vertex_word_support extent tags edges).scalar spin
  have ht := ledger_word extent tags edges hp
  have htScalar : PaddedPolynomialCoeffEqv (linkCount extent+3)
      (slabGaugeQuaternion extent tags (liftThree (word extent edges))).scalar
      (wordWith (vertexEntry extent tags) edges).scalar := ht.scalar
  have image := (padded_apply (by omega : 0 < linkCount extent+2) (Steps extent tags)
    (lift_character (linkCount extent+3) 3 (word extent edges).scalar spin)).trans
      ((applySteps_character (by omega : 0 < linkCount extent+2) (Steps extent tags)
        (liftThree (word extent edges)).scalar spin).trans (htScalar.character spin))
  have cancel := SU2QuaternionHaarGaugeWord.closed_character
    (fun v => auxiliaryGauge (tags v)) (fun _ => auxiliaryGauge_unit extent _)
    start (pathData extent edges) ((path_finish extent start edges).trans hclosed) spin
  have front := characterPolynomial_coeffEqv (vertex_word extent tags start edges hc).scalar spin
  have liftedScalar : PaddedPolynomialCoeffEqv (linkCount extent+3)
      (liftThree (word extent edges)).scalar
      (SU2QuaternionHaarGaugeWord.word (pathData extent edges)).scalar :=
    (lifted_word extent edges).scalar
  have back := (lift_character (linkCount extent+3) 3 (word extent edges).scalar spin).trans
    (liftedScalar.character spin)
  refine ⟨hs, ?_⟩
  exact (SupportedHaarEqv.of_padded image hg hv).trans
    ((SupportedHaarEqv.of_carrier (HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier front) cancel)).trans
      (SupportedHaarEqv.of_padded back hl
        (SU2QuaternionRelativeHeatPairGeometry.character_supported
          (path_word_support extent edges).scalar spin)).symm)

/-- Concrete original SourceLoop placement; both carrier-room guards are retained. -/
theorem placedSourceLoop_invariant {width time extent : Nat} (hw : width ≤ extent)
    (ht : time ≤ extent) (loop : SourceLoop width)
    (tags : Z4Vertex → Option (Fin 3)) (spin : Nat) :
    Invariant extent tags (character extent (loop.edges.map (shiftEntry time)) spin) := by
  let placed := placeLoop hw ht loop
  exact closedWord_invariant extent tags placed.start placed.edges
    placed.compatible placed.closed placed.physical spin

/-- Finite signed sums/products of actually placed closed Wilson words. -/
theorem placedWindow_invariant {width start L extent : Nat} (hw : width ≤ extent)
    (ht : start+L ≤ extent) (tags : Z4Vertex → Option (Fin 3)) :
    ∀ e : WindowExpression width, Within L e → Invariant extent tags (placedPolynomial extent start e)
  | .one, _ => Invariant.one extent tags
  | .loop offset value spin, h => by
      have hoffset : offset ≤ L := h
      exact placedSourceLoop_invariant hw (by omega) value tags spin
  | .add e f, h => (placedWindow_invariant hw ht tags e h.1).add
      (placedWindow_invariant hw ht tags f h.2)
  | .mul e f, h => (placedWindow_invariant hw ht tags e h.1).mul
      (placedWindow_invariant hw ht tags f h.2)
  | .smul c e, h => (placedWindow_invariant hw ht tags e h).smul c

end YMGap.Continuum.BF4ExactSlabVertexGaugeWilsonWord

#print axioms YMGap.Continuum.BF4ExactSlabVertexGaugeWilsonWord.closedWord_invariant
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaugeWilsonWord.placedSourceLoop_invariant
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaugeWilsonWord.placedWindow_invariant
