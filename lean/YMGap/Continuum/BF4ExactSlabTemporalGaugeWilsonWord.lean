/-
# Literal closed spatial Wilson words under the common temporal ledger

The observable is the ordered product of actual original slab link
polynomials, with inverse orientation retained. Endpoint compatibility,
closedness, physical carrier membership and the common spatial slice are
finite geometric data. The existing ONE temporal ledger acts on every edge;
its upper vertex gauges telescope and its lower edges are unchanged.

The final invariant retains every supported spectator insertion. Padding is
removed only with the actual support proofs. No plaquette-trace recoding,
union embedding, OS density, enlarged-carrier gap or continuum claim is made.
-/

import YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages
import YMGap.Continuum.SU2QuaternionHaarGaugeWord
import YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation

namespace YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFixedCoordinates
open YMGap.Continuum.BF4ExactSlabTemporalGaugeUpperCoordinates
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation "B" extent => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv

def entryStart (e : OrientedBF4Link) : Z4Vertex :=
  if e.reverse then addE e.link.1 e.link.2 else e.link.1

def entryFinish (e : OrientedBF4Link) : Z4Vertex :=
  if e.reverse then e.link.1 else addE e.link.1 e.link.2

def pathFinish (start : Z4Vertex) : List OrientedBF4Link → Z4Vertex
  | [] => start
  | e :: es => pathFinish (entryFinish e) es

/-- Consecutive factors share the actual oriented lattice endpoint. -/
def Compatible (start : Z4Vertex) : List OrientedBF4Link → Prop
  | [] => True
  | e :: es => entryStart e = start ∧ Compatible (entryFinish e) es

/-- All data are original finite lattice geometry, not an analytic premise. -/
structure SpatialLoop (extent slice : Nat) where
  start : Z4Vertex
  edges : List OrientedBF4Link
  compatible : Compatible start edges
  closed : pathFinish start edges = start
  physical : ∀ e, e ∈ edges → e.link ∈ boundaryCompleteSlabLinks extent
  spatial : ∀ e, e ∈ edges → e.link.2 ≠ .x3 ∧ e.link.1.2.2.2 = slice

def wordWith (value : OrientedBF4Link → PolyQuaternion) : List OrientedBF4Link → PolyQuaternion
  | [] => PolyQuaternion.one
  | e :: es => PolyQuaternion.mul (value e) (wordWith value es)

/-- The literal original ordered word, not a product of individual traces. -/
def word (extent : Nat) (edges : List OrientedBF4Link) : PolyQuaternion :=
  wordWith (orientedCorrectedSlabLinkPolynomial extent) edges

def character (extent : Nat) (edges : List OrientedBF4Link) (spin : Nat) : RatPoly :=
  characterPolynomial (word extent edges).scalar spin

def temporalEntry (extent cut : Nat) (e : OrientedBF4Link) : PolyQuaternion :=
  if e.reverse then PolyQuaternion.conj (upperTemporalLink extent cut e.link)
  else upperTemporalLink extent cut e.link

def temporalWord (extent cut : Nat) (edges : List OrientedBF4Link) : PolyQuaternion :=
  wordWith (temporalEntry extent cut) edges

private theorem support_one (blocks : Nat) : QuaternionSupported blocks PolyQuaternion.one :=
  ⟨supported_one blocks, (fun _ h => False.elim (List.not_mem_nil h)),
    (fun _ h => False.elim (List.not_mem_nil h)),
    (fun _ h => False.elim (List.not_mem_nil h))⟩

theorem link_supported (extent : Nat) (link : Z4Link) :
    QuaternionSupported (B extent) (correctedSlabLinkPolynomial extent link) := by
  by_cases h : link ∈ boundaryCompleteSlabLinks extent
  · rw [correctedSlabLinkPolynomial_of_mem h]
    exact QuaternionSupported.coordinate (List.idxOf_lt_length_of_mem h)
  · rw [correctedSlabLinkPolynomial_of_not_mem h]
    exact support_one _

theorem oriented_supported (extent : Nat) (e : OrientedBF4Link) :
    QuaternionSupported (B extent) (orientedCorrectedSlabLinkPolynomial extent e) := by
  unfold orientedCorrectedSlabLinkPolynomial
  split
  · exact (link_supported extent e.link).conj
  · exact link_supported extent e.link

private theorem wordWith_supported {blocks : Nat} (value : OrientedBF4Link → PolyQuaternion)
    (h : ∀ e, QuaternionSupported blocks (value e)) : ∀ edges : List OrientedBF4Link,
    QuaternionSupported blocks (wordWith value edges)
  | [] => support_one _
  | e :: es => (h e).mul (wordWith_supported value h es)

theorem word_supported (extent : Nat) (edges : List OrientedBF4Link) :
    QuaternionSupported (B extent) (word extent edges) :=
  wordWith_supported _ (oriented_supported extent) edges

theorem character_supported (extent : Nat) (edges : List OrientedBF4Link) (spin : Nat) :
    SupportedQuaternionBlocks (B extent) (character extent edges spin) :=
  SU2QuaternionRelativeHeatPairGeometry.character_supported (word_supported extent edges).scalar spin

private theorem temporalEntry_supported (extent cut : Nat) (e : OrientedBF4Link) :
    QuaternionSupported (B extent) (temporalEntry extent cut e) := by
  have h : QuaternionSupported (B extent) (upperTemporalLink extent cut e.link) := by
    unfold upperTemporalLink
    split
    · exact ((link_supported extent (fixedTimeLink cut e.link.1)).conj.mul
        (link_supported extent e.link)).mul
          (link_supported extent (fixedTimeLink cut (addE e.link.1 e.link.2)))
    · exact link_supported extent e.link
  unfold temporalEntry
  split
  · exact h.conj
  · exact h

theorem temporalWord_supported (extent cut : Nat) (edges : List OrientedBF4Link) :
    QuaternionSupported (B extent) (temporalWord extent cut edges) :=
  wordWith_supported _ (temporalEntry_supported extent cut) edges

theorem ledger_entry {extent cut : Nat} {e : OrientedBF4Link}
    (he : e.link ∈ boundaryCompleteSlabLinks extent) :
    PaddedQuaternionCoeffEqv (B extent)
      (applyTemporalLedgerQuaternion extent cut (orientedCorrectedSlabLinkPolynomial extent e))
      (temporalEntry extent cut e) := by
  have h := temporalLedger_assignment (half := cut) he
  unfold orientedCorrectedSlabLinkPolynomial temporalEntry
  split
  · have hc := applySteps_conj (temporalTailBlocks_pos extent) (temporalTranslationSteps extent cut)
      (correctedSlabLinkPolynomial extent e.link)
    rw [temporalTotalBlocks_eq] at hc
    exact hc.trans h.conj
  · exact h

/-- The entire original ledger, with every original edge and inverse orientation. -/
theorem ledger_word (extent cut : Nat) : ∀ edges : List OrientedBF4Link,
    (∀ e, e ∈ edges → e.link ∈ boundaryCompleteSlabLinks extent) →
    PaddedQuaternionCoeffEqv (B extent)
      (applyTemporalLedgerQuaternion extent cut (word extent edges))
      (temporalWord extent cut edges)
  | [], _ => by
      have h := applySteps_one (temporalTailBlocks_pos extent) (temporalTranslationSteps extent cut)
      rw [temporalTotalBlocks_eq] at h
      exact h
  | e :: es, hp => by
      have h := applySteps_mul (temporalTailBlocks_pos extent) (temporalTranslationSteps extent cut)
        (orientedCorrectedSlabLinkPolynomial extent e) (word extent es)
      rw [temporalTotalBlocks_eq] at h
      exact h.trans ((ledger_entry (hp e List.mem_cons_self)).mul
        (ledger_word extent cut es (fun f hf => hp f (List.mem_cons_of_mem e hf))))

theorem ledger_character (extent cut : Nat) (edges : List OrientedBF4Link)
    (hp : ∀ e, e ∈ edges → e.link ∈ boundaryCompleteSlabLinks extent) (spin : Nat) :
    PaddedPolynomialCoeffEqv (B extent)
      (applyTemporalTranslationLedger extent cut (character extent edges spin))
      (characterPolynomial (temporalWord extent cut edges).scalar spin) := by
  have h := applySteps_character (temporalTailBlocks_pos extent) (temporalTranslationSteps extent cut)
    (word extent edges).scalar spin
  rw [temporalTotalBlocks_eq] at h
  exact h.trans (PaddedPolynomialCoeffEqv.character (ledger_word extent cut edges hp).scalar spin)

private def pathData (extent : Nat) (edges : List OrientedBF4Link) : List (PolyQuaternion × Z4Vertex) :=
  edges.map (fun e => (orientedCorrectedSlabLinkPolynomial extent e, entryFinish e))

private theorem pathData_word (extent : Nat) : ∀ edges : List OrientedBF4Link,
    SU2QuaternionHaarGaugeWord.word (pathData extent edges) = word extent edges
  | [] => rfl
  | _ :: es => congrArg (PolyQuaternion.mul _) (pathData_word extent es)

private theorem pathData_finish (extent : Nat) (start : Z4Vertex) : ∀ edges : List OrientedBF4Link,
    SU2QuaternionHaarGaugeWord.finish start (pathData extent edges) = pathFinish start edges
  | [] => rfl
  | e :: es => pathData_finish extent (entryFinish e) es

private theorem upper_entry (extent cut : Nat) (e : OrientedBF4Link)
    (hu : linkHalfSide cut e.link = .upper) :
    PolyQuaternionCoeffEqv (temporalEntry extent cut e)
      (gaugeLink (temporalVertexGauge extent cut (entryStart e))
        (orientedCorrectedSlabLinkPolynomial extent e)
        (temporalVertexGauge extent cut (entryFinish e))) := by
  unfold temporalEntry upperTemporalLink entryStart entryFinish orientedCorrectedSlabLinkPolynomial
  rw [if_pos hu]
  cases hr : e.reverse
  · exact PolyQuaternionCoeffEqv.refl _
  · exact gaugeLink_conj _ _ _

private theorem upper_word (extent cut : Nat) (start : Z4Vertex) :
    ∀ edges : List OrientedBF4Link, Compatible start edges →
    (∀ e, e ∈ edges → linkHalfSide cut e.link = .upper) →
    PolyQuaternionCoeffEqv (temporalWord extent cut edges)
      (SU2QuaternionHaarGaugeWord.gaugeWord (temporalVertexGauge extent cut) start (pathData extent edges))
  | [], _, _ => PolyQuaternionCoeffEqv.refl _
  | e :: es, hc, hu => by
      have he := upper_entry extent cut e (hu e List.mem_cons_self)
      rw [hc.1] at he
      exact he.mul (upper_word extent cut (entryFinish e) es hc.2
        (fun f hf => hu f (List.mem_cons_of_mem e hf)))

/-- Arbitrary closed physical upper words, not merely four-edge faces. -/
theorem upper_closed_character (extent cut : Nat) (start : Z4Vertex)
    (edges : List OrientedBF4Link) (hc : Compatible start edges)
    (hclosed : pathFinish start edges = start)
    (hu : ∀ e, e ∈ edges → linkHalfSide cut e.link = .upper) (spin : Nat) :
    HaarCarrierEqv (B extent) (characterPolynomial (temporalWord extent cut edges).scalar spin)
      (character extent edges spin) := by
  have h := SU2QuaternionHaarGaugeWord.closed_character (temporalVertexGauge extent cut)
    (temporalVertexGauge_haar_unit extent cut) start (pathData extent edges)
    ((pathData_finish extent start edges).trans hclosed) spin
  rw [pathData_word] at h
  exact HaarCarrierEqv.trans
    (RatPolyCoeffEqv.haarCarrier
      (characterPolynomial_coeffEqv (upper_word extent cut start edges hc hu).scalar spin)) h

theorem lower_unchanged (extent cut : Nat) : ∀ edges : List OrientedBF4Link,
    (∀ e, e ∈ edges → linkHalfSide cut e.link ≠ .upper) →
    temporalWord extent cut edges = word extent edges
  | [], _ => rfl
  | e :: es, hn => by
      have he : temporalEntry extent cut e = orientedCorrectedSlabLinkPolynomial extent e := by
        unfold temporalEntry upperTemporalLink orientedCorrectedSlabLinkPolynomial
        rw [if_neg (hn e List.mem_cons_self)]
      change PolyQuaternion.mul (temporalEntry extent cut e) (temporalWord extent cut es) =
        PolyQuaternion.mul (orientedCorrectedSlabLinkPolynomial extent e) (word extent es)
      rw [he, lower_unchanged extent cut es (fun f hf => hn f (List.mem_cons_of_mem e hf))]

private theorem spatial_side (cut slice : Nat) (link : Z4Link)
    (hs : link.2 ≠ .x3) (ht : link.1.2.2.2 = slice) :
    linkHalfSide cut link = spatialHalfSide cut slice := by
  rcases link with ⟨⟨x,y,z,t⟩,dir⟩
  cases dir <;> simp_all [linkHalfSide]

/-- A same-slice closed word is below or above every cut, so every cut preserves it. -/
theorem closed_spatial_character_invariant {extent slice : Nat}
    (loop : SpatialLoop extent slice) (cut spin : Nat) :
    HaarCarrierEqv (B extent)
      (characterPolynomial (temporalWord extent cut loop.edges).scalar spin)
      (character extent loop.edges spin) := by
  by_cases ht : slice ≤ cut
  · have hn : ∀ e, e ∈ loop.edges → linkHalfSide cut e.link ≠ .upper := by
      intro e he
      rw [spatial_side cut slice e.link (loop.spatial e he).1 (loop.spatial e he).2,
        spatialHalfSide, if_pos ht]
      decide
    rw [lower_unchanged extent cut loop.edges hn]
    exact HaarCarrierEqv.refl _ _
  · apply upper_closed_character extent cut loop.start loop.edges loop.compatible loop.closed
    intro e he
    rw [spatial_side cut slice e.link (loop.spatial e he).1 (loop.spatial e he).2,
      spatialHalfSide, if_neg ht]

/-- Exact input for the whole-action sweep: every supported spectator stays present. -/
theorem ledger_invariant {extent slice : Nat} (loop : SpatialLoop extent slice)
    (cut spin : Nat) (r : RatPoly) (hr : SupportedQuaternionBlocks (B extent) r) :
    quaternionHaar (B extent)
        (polyMul r (applyTemporalTranslationLedger extent cut (character extent loop.edges spin))) ≈
      quaternionHaar (B extent) (polyMul r (character extent loop.edges spin)) := by
  have hp := character_supported extent loop.edges spin
  have ht := SU2QuaternionRelativeHeatPairGeometry.character_supported
    (temporalWord_supported extent cut loop.edges).scalar spin
  exact Q'.eqv_trans _ _ _
    ((ledger_character extent cut loop.edges loop.physical spin).haar_insert
      (applyTemporalTranslationLedger_supported extent cut _ hp) ht r hr)
    (closed_spatial_character_invariant loop cut spin r)

#print axioms entryStart
#print axioms entryFinish
#print axioms pathFinish
#print axioms Compatible
#print axioms SpatialLoop
#print axioms wordWith
#print axioms word
#print axioms character
#print axioms temporalEntry
#print axioms temporalWord
#print axioms link_supported
#print axioms oriented_supported
#print axioms word_supported
#print axioms character_supported
#print axioms temporalWord_supported
#print axioms ledger_entry
#print axioms ledger_word
#print axioms ledger_character
#print axioms upper_closed_character
#print axioms lower_unchanged
#print axioms closed_spatial_character_invariant
#print axioms ledger_invariant

end YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
