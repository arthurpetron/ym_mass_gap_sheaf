/-
# Literal site reflection and one-sidedness of original spatial Wilson words

Reflection acts on the actual corrected-slab link coordinates. Spatial links
retain their traversal orientation and their quaternion multiplication order.
A placed source loop is therefore reflected by its literal time placement,
not by replacing its trace with a product of elementary plaquette traces.

The lower word is syntactically one-sided on the same even slab, including
its shared central slice. These are the geometric inputs to the existing
selected-action OS reflected-square theorem, not an independent L2 argument.
No union embedding, completed-space gap or continuum result is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection

namespace YMGap.Continuum.BF4ExactSlabSpatialWilsonReflection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization
open YMGap.Continuum.BF4ExactSlabSiteConditionalSquare
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection (symmetric_window_contained)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

local notation:max "E" radius:arg => adjacentEvenExtent radius
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- A spatial reflection changes the actual link, not its traversal orientation. -/
def reflectEntry (extent : Nat) (e : OrientedBF4Link) : OrientedBF4Link :=
  ⟨timeReflectLink extent e.link, e.reverse⟩

private structure QuaternionImage (extent : Nat) (p q : PolyQuaternion) : Prop where
  scalar : ReflectionImage extent p.scalar q.scalar
  iPart : ReflectionImage extent p.iPart q.iPart
  jPart : ReflectionImage extent p.jPart q.jPart
  kPart : ReflectionImage extent p.kPart q.kPart

private theorem image_one (extent : Nat) : QuaternionImage extent PolyQuaternion.one PolyQuaternion.one :=
  ⟨ReflectionImage.one extent, ReflectionImage.zero extent,
    ReflectionImage.zero extent, ReflectionImage.zero extent⟩

private theorem QuaternionImage.conj {extent : Nat} {p q : PolyQuaternion}
    (h : QuaternionImage extent p q) :
    QuaternionImage extent (PolyQuaternion.conj p) (PolyQuaternion.conj q) :=
  ⟨h.scalar, h.iPart.neg, h.jPart.neg, h.kPart.neg⟩

private theorem QuaternionImage.mul {extent : Nat} {p p' q q' : PolyQuaternion}
    (hp : QuaternionImage extent p p') (hq : QuaternionImage extent q q') :
    QuaternionImage extent (PolyQuaternion.mul p q) (PolyQuaternion.mul p' q') :=
  ⟨(hp.scalar.mul hq.scalar).add
      ((hp.iPart.mul hq.iPart).add ((hp.jPart.mul hq.jPart).add (hp.kPart.mul hq.kPart))).neg,
    (hp.scalar.mul hq.iPart).add ((hp.iPart.mul hq.scalar).add
      ((hp.jPart.mul hq.kPart).add (hp.kPart.mul hq.jPart).neg)),
    (hp.scalar.mul hq.jPart).add ((hp.jPart.mul hq.scalar).add
      ((hp.kPart.mul hq.iPart).add (hp.iPart.mul hq.kPart).neg)),
    (hp.scalar.mul hq.kPart).add ((hp.kPart.mul hq.scalar).add
      ((hp.iPart.mul hq.jPart).add (hp.jPart.mul hq.iPart).neg))⟩

attribute [local irreducible] correctedSlabLinkPolynomial

private theorem entry_reflection {extent : Nat} {e : OrientedBF4Link}
    (hp : e.link ∈ boundaryCompleteSlabLinks extent) (hs : e.link.2 ≠ .x3) :
    QuaternionImage extent (orientedCorrectedSlabLinkPolynomial extent e)
      (orientedCorrectedSlabLinkPolynomial extent (reflectEntry extent e)) := by
  have h := spatial_link_reflection hp hs
  have hi : QuaternionImage extent (correctedSlabLinkPolynomial extent e.link)
      (correctedSlabLinkPolynomial extent (timeReflectLink extent e.link)) :=
    ⟨h.scalar, h.iPart, h.jPart, h.kPart⟩
  unfold orientedCorrectedSlabLinkPolynomial reflectEntry
  cases hr : e.reverse
  · simpa only [Bool.false_eq_true, ↓reduceIte] using hi
  · simpa only [↓reduceIte] using hi.conj

private theorem word_reflection (extent : Nat) : ∀ edges : List OrientedBF4Link,
    (∀ e, e ∈ edges → e.link ∈ boundaryCompleteSlabLinks extent) →
    (∀ e, e ∈ edges → e.link.2 ≠ .x3) →
    QuaternionImage extent (word extent edges) (word extent (edges.map (reflectEntry extent)))
  | [], _, _ => image_one extent
  | e :: es, hp, hs => (entry_reflection (hp e List.mem_cons_self) (hs e List.mem_cons_self)).mul
      (word_reflection extent es (fun f hf => hp f (List.mem_cons_of_mem e hf))
        (fun f hf => hs f (List.mem_cons_of_mem e hf)))

/-- Arbitrary ordered spatial words and all character spins on the original slab. -/
theorem spatial_character_reflection (extent : Nat) (edges : List OrientedBF4Link)
    (hp : ∀ e, e ∈ edges → e.link ∈ boundaryCompleteSlabLinks extent)
    (hs : ∀ e, e ∈ edges → e.link.2 ≠ .x3) (spin : Nat) :
    ReflectionImage extent (character extent edges spin)
      (character extent (edges.map (reflectEntry extent)) spin) :=
  (PaddedPolynomialCoeffEqv.of_prefix
    (reflectCorrectedSlabPolynomial_character_prefix extent (word extent edges).scalar spin)).trans
      (PaddedPolynomialCoeffEqv.character (word_reflection extent edges hp hs).scalar spin)

private theorem shifted_entry_reflection {width radius A h j : Nat}
    (hcenter : A+h=radius+1) (hj : j ≤ h) {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) :
    reflectEntry (E radius) (shiftEntry (A+j) e) = shiftEntry (A+(2*h-j)) e := by
  have hd := (baseLinks_mem_iff width e.link).mp he
  have hsp := hd.1
  have hz := hd.2.2.2.2
  rcases e with ⟨⟨⟨x,y,z,t⟩,dir⟩,reverse⟩
  change t = 0 at hz
  subst t
  have ht : E radius - (A+j) = A+(2*h-j) := by
    unfold adjacentEvenExtent centralExtent
    omega
  cases dir <;> try exact False.elim (hsp rfl)
  all_goals simp only [reflectEntry, shiftEntry, timeShiftLink, timeShiftVertex,
    timeReflectLink, Nat.zero_add, ht]

/-- The literal site reflection changes only the scheduled placement time. -/
theorem placed_reflection {width radius A h j : Nat}
    (hw : width ≤ E radius) (hcenter : A+h=radius+1) (hj : j ≤ h)
    (loop : SourceLoop width) (spin : Nat) :
    ReflectionImage (E radius)
      (character (E radius) (loop.edges.map (shiftEntry (A+j))) spin)
      (character (E radius) (loop.edges.map (shiftEntry (A+(2*h-j)))) spin) := by
  have ht : A+j ≤ E radius := by have := symmetric_window_contained hcenter; omega
  let hp := placeLoop hw ht loop
  have hr := spatial_character_reflection (E radius) hp.edges hp.physical
    (fun e he => (hp.spatial e he).1) spin
  have he : (loop.edges.map (shiftEntry (A+j))).map (reflectEntry (E radius)) =
      loop.edges.map (shiftEntry (A+(2*h-j))) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro e he
    exact shifted_entry_reflection hcenter hj (loop.physical e he)
  change ReflectionImage (E radius)
    (character (E radius) (loop.edges.map (shiftEntry (A+j))) spin)
    (character (E radius) ((loop.edges.map (shiftEntry (A+j))).map (reflectEntry (E radius))) spin) at hr
  rw [he] at hr
  exact hr

private structure OneSidedQuaternion (radius : Nat) (q : PolyQuaternion) : Prop where
  scalar : OneSided radius q.scalar
  iPart : OneSided radius q.iPart
  jPart : OneSided radius q.jPart
  kPart : OneSided radius q.kPart

private theorem local_one (radius : Nat) : OneSidedQuaternion radius PolyQuaternion.one :=
  ⟨BlockLocal.one _ _, BlockLocal.zero _ _, BlockLocal.zero _ _, BlockLocal.zero _ _⟩

private theorem OneSidedQuaternion.conj {radius : Nat} {q : PolyQuaternion}
    (h : OneSidedQuaternion radius q) : OneSidedQuaternion radius (PolyQuaternion.conj q) :=
  ⟨h.scalar, BlockLocal.neg h.iPart, BlockLocal.neg h.jPart, BlockLocal.neg h.kPart⟩

private theorem OneSidedQuaternion.mul {radius : Nat} {p q : PolyQuaternion}
    (hp : OneSidedQuaternion radius p) (hq : OneSidedQuaternion radius q) :
    OneSidedQuaternion radius (PolyQuaternion.mul p q) := by
  constructor <;> simp only [PolyQuaternion.mul]
  all_goals repeat' first
    | exact hp.scalar | exact hp.iPart | exact hp.jPart | exact hp.kPart
    | exact hq.scalar | exact hq.iPart | exact hq.jPart | exact hq.kPart
    | apply BlockLocal.add | apply BlockLocal.neg | apply BlockLocal.mul

private theorem link_oneSided (radius : Nat) (link : Z4Link)
    (hs : adjacentEvenLinkSide radius link ≠ .upper) :
    OneSidedQuaternion radius (correctedSlabLinkPolynomial (E radius) link) := by
  by_cases hm : link ∈ boundaryCompleteSlabLinks (E radius)
  · have hc (c : Nat) (h : c < 4) :
        OneSided radius (polyVar (4*(boundaryCompleteSlabLinks (E radius)).idxOf link+c)) := by
      apply BlockLocal.coordinate
      rw [show (4*(boundaryCompleteSlabLinks (E radius)).idxOf link+c)/4 =
        (boundaryCompleteSlabLinks (E radius)).idxOf link by omega]
      unfold blockSide
      rw [correctedSlabLinkAt_idxOf hm]
      exact hs
    rw [correctedSlabLinkPolynomial_of_mem hm]
    exact ⟨hc 0 (by omega), hc 1 (by omega), hc 2 (by omega), hc 3 (by omega)⟩
  · rw [correctedSlabLinkPolynomial_of_not_mem hm]
    exact local_one radius

private theorem entry_oneSided (radius : Nat) (e : OrientedBF4Link)
    (hs : adjacentEvenLinkSide radius e.link ≠ .upper) :
    OneSidedQuaternion radius (orientedCorrectedSlabLinkPolynomial (E radius) e) := by
  unfold orientedCorrectedSlabLinkPolynomial
  split
  · exact (link_oneSided radius e.link hs).conj
  · exact link_oneSided radius e.link hs

private theorem word_oneSided (radius : Nat) : ∀ edges : List OrientedBF4Link,
    (∀ e, e ∈ edges → adjacentEvenLinkSide radius e.link ≠ .upper) →
    OneSidedQuaternion radius (word (E radius) edges)
  | [], _ => local_one radius
  | e :: es, hs => (entry_oneSided radius e (hs e List.mem_cons_self)).mul
      (word_oneSided radius es (fun f hf => hs f (List.mem_cons_of_mem e hf)))

theorem character_oneSided (radius : Nat) (edges : List OrientedBF4Link)
    (hs : ∀ e, e ∈ edges → adjacentEvenLinkSide radius e.link ≠ .upper) (spin : Nat) :
    OneSided radius (character (E radius) edges spin) :=
  BlockLocal.character (word_oneSided radius edges hs).scalar spin

private theorem spatial_not_upper {radius : Nat} {link : Z4Link}
    (hsp : link.2 ≠ .x3) (ht : link.1.2.2.2 ≤ radius+1) :
    adjacentEvenLinkSide radius link ≠ .upper := by
  rcases link with ⟨⟨x,y,z,time⟩,dir⟩
  change time ≤ radius+1 at ht
  cases dir <;> try exact False.elim (hsp rfl)
  all_goals change adjacentEvenSpatialSide radius time ≠ .upper
  all_goals
    by_cases hl : time < radius+1
    · simp [adjacentEvenSpatialSide, adjacentEvenCenter, hl]
    · have he : time=radius+1 := by omega
      simp [adjacentEvenSpatialSide, adjacentEvenCenter, he]

/-- Same physical lower word, with central-slice links allowed. -/
theorem placed_oneSided {width radius A h j : Nat}
    (hw : width ≤ E radius) (hcenter : A+h=radius+1) (hj : j ≤ h)
    (loop : SourceLoop width) (spin : Nat) :
    OneSided radius (character (E radius) (loop.edges.map (shiftEntry (A+j))) spin) := by
  have ht : A+j ≤ E radius := by have := symmetric_window_contained hcenter; omega
  let hp := placeLoop hw ht loop
  apply character_oneSided
  intro e he
  have hs := hp.spatial e he
  apply spatial_not_upper hs.1
  rw [hs.2]
  omega

#print axioms reflectEntry
#print axioms spatial_character_reflection
#print axioms placed_reflection
#print axioms character_oneSided
#print axioms placed_oneSided

end YMGap.Continuum.BF4ExactSlabSpatialWilsonReflection
