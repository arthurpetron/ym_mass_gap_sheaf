/-
# Literal oriented plaquette reflection at every extent

Spatial links are reflected without conjugation; time links acquire precisely
their three vector-coordinate signs. The ordered reflected temporal word is
the cyclic inverse of the original reflected face word. Its scalar identity
is a coefficient theorem for four arbitrary polynomial quaternions, not a
scan of the slab. All-spin characters retain that identity on the same padded
carrier. No positivity, norm-one assumption or new physical law is used.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm

namespace YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionCoordinateConjugation
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

theorem time_coordinate_reflection_prefix {extent block : Nat}
    (hb : block ∈ correctedSlabLinkBlocks extent)
    (ht : (correctedSlabLinkAt extent block).2 = .x3) (component : Nat) (hc : component < 4) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks extent).length
      (reflectCorrectedSlabPolynomial extent (polyVar (4 * block + component)))
      (if component = 0 then polyVar (4 * correctedSlabLinkReflectBlock extent block + component)
        else polyNeg (polyVar (4 * correctedSlabLinkReflectBlock extent block + component))) := by
  have h := (reindex_coordinate_prefix (correctedSlabQuaternionBlockInvolution extent)
    block (correctedSlabLinkBlock_lt hb) component hc).signSelected (correctedSlabTimeVectorCoordinate extent)
  change QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks extent).length
    (reflectCorrectedSlabPolynomial extent (polyVar (4 * block + component)))
    (signSelectedPolynomial (4 * (boundaryCompleteSlabLinks extent).length)
      (correctedSlabTimeVectorCoordinate extent)
      (polyVar (4 * correctedSlabLinkReflectBlock extent block + component))) at h
  have hi := correctedSlabLinkBlock_lt (correctedSlabLinkReflectBlock_physical hb)
  have hs : correctedSlabTimeVectorCoordinate extent
      (4 * correctedSlabLinkReflectBlock extent block + component) = decide (component ≠ 0) := by
    unfold correctedSlabTimeVectorCoordinate
    rw [show (4 * correctedSlabLinkReflectBlock extent block + component) / 4 =
      correctedSlabLinkReflectBlock extent block by omega,
      show (4 * correctedSlabLinkReflectBlock extent block + component) % 4 = component by omega,
      correctedSlabLinkAt_reflectBlock hb, timeReflectLink_direction, ht]
    simp
  rw [signSelectedPolynomial_var _ _ _ (by omega), hs] at h
  by_cases hz : component = 0 <;> simpa [hz] using h

/-- A physical time link is reflected with quaternion conjugation, at every
extent. This is all four coefficient-sensitive coordinate identities. -/
theorem time_link_reflection {extent : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) (ht : link.2 = .x3) :
    PaddedQuaternionCoeffEqv (boundaryCompleteSlabLinks extent).length
      (reflectSlabQuaternion extent (correctedSlabLinkPolynomial extent link))
      (PolyQuaternion.conj (correctedSlabLinkPolynomial extent (timeReflectLink extent link))) := by
  have hb : (boundaryCompleteSlabLinks extent).idxOf link ∈ correctedSlabLinkBlocks extent :=
    List.mem_range.mpr (List.idxOf_lt_length_of_mem hl)
  have htime : (correctedSlabLinkAt extent ((boundaryCompleteSlabLinks extent).idxOf link)).2 = .x3 := by
    rw [correctedSlabLinkAt_idxOf hl]
    exact ht
  have coordinate (i : Nat) (hi : i < 4) := time_coordinate_reflection_prefix hb htime i hi
  simp only [reflectedBlock_idxOf hl] at coordinate
  rw [correctedSlabLinkPolynomial_of_mem hl,
    correctedSlabLinkPolynomial_of_mem (timeReflectLink_mem_boundaryCompleteSlabLinks hl)]
  apply PaddedQuaternionCoeffEqv.of_prefix
  exact ⟨coordinate 0 (by omega), coordinate 1 (by omega), coordinate 2 (by omega), coordinate 3 (by omega)⟩

private def orientedFor (u : Z4Link → PolyQuaternion) (extent : Nat) (link : Z4Link) : PolyQuaternion :=
  if link.2 = .x3 then PolyQuaternion.conj (u (timeReflectLink extent link))
  else u (timeReflectLink extent link)

/-- The original reflected link, with its geometric orientation retained. -/
def orientedReflectedLink (extent : Nat) (link : Z4Link) : PolyQuaternion :=
  orientedFor (correctedSlabLinkPolynomial extent) extent link

private structure QImage (extent : Nat) (p q : PolyQuaternion) : Prop where
  scalar : ReflectionImage extent p.scalar q.scalar
  iPart : ReflectionImage extent p.iPart q.iPart
  jPart : ReflectionImage extent p.jPart q.jPart
  kPart : ReflectionImage extent p.kPart q.kPart

private theorem QImage.of_padded {extent : Nat} {p q : PolyQuaternion}
    (h : PaddedQuaternionCoeffEqv (boundaryCompleteSlabLinks extent).length (reflectSlabQuaternion extent p) q) :
    QImage extent p q := ⟨h.scalar, h.iPart, h.jPart, h.kPart⟩

private theorem QImage.trans_coeff {extent : Nat} {p q r : PolyQuaternion}
    (hp : QImage extent p q) (hq : PolyQuaternionCoeffEqv q r) : QImage extent p r :=
  ⟨hp.scalar.trans (.of_coeff hq.scalar), hp.iPart.trans (.of_coeff hq.iPart),
    hp.jPart.trans (.of_coeff hq.jPart), hp.kPart.trans (.of_coeff hq.kPart)⟩

theorem link_reflection {extent : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    QImage extent (correctedSlabLinkPolynomial extent link) (orientedReflectedLink extent link) := by
  unfold orientedReflectedLink orientedFor
  split
  · exact QImage.of_padded (time_link_reflection hl ‹_›)
  · exact QImage.of_padded (spatial_link_reflection hl ‹_›)

private theorem image_one (extent : Nat) : QImage extent PolyQuaternion.one PolyQuaternion.one :=
  ⟨ReflectionImage.one extent, ReflectionImage.zero extent, ReflectionImage.zero extent, ReflectionImage.zero extent⟩

private theorem image_conj {extent : Nat} {p q : PolyQuaternion} (h : QImage extent p q) :
    QImage extent (PolyQuaternion.conj p) (PolyQuaternion.conj q) := by
  have hs : ReflectionImage extent p.scalar q.scalar := h.scalar
  have hi : ReflectionImage extent p.iPart q.iPart := h.iPart
  have hj : ReflectionImage extent p.jPart q.jPart := h.jPart
  have hk : ReflectionImage extent p.kPart q.kPart := h.kPart
  exact ⟨hs, hi.neg, hj.neg, hk.neg⟩

private theorem image_mul {extent : Nat} {p p' q q' : PolyQuaternion}
    (hp : QImage extent p p') (hq : QImage extent q q') :
    QImage extent (PolyQuaternion.mul p q) (PolyQuaternion.mul p' q') := by
  have ps : ReflectionImage extent p.scalar p'.scalar := hp.scalar
  have pi : ReflectionImage extent p.iPart p'.iPart := hp.iPart
  have pj : ReflectionImage extent p.jPart p'.jPart := hp.jPart
  have pk : ReflectionImage extent p.kPart p'.kPart := hp.kPart
  have qs : ReflectionImage extent q.scalar q'.scalar := hq.scalar
  have qi : ReflectionImage extent q.iPart q'.iPart := hq.iPart
  have qj : ReflectionImage extent q.jPart q'.jPart := hq.jPart
  have qk : ReflectionImage extent q.kPart q'.kPart := hq.kPart
  exact ⟨(ps.mul qs).add ((pi.mul qi).add ((pj.mul qj).add (pk.mul qk))).neg,
    (ps.mul qi).add ((pi.mul qs).add ((pj.mul qk).add (pk.mul qj).neg)),
    (ps.mul qj).add ((pj.mul qs).add ((pk.mul qi).add (pi.mul qk).neg)),
    (ps.mul qk).add ((pk.mul qs).add ((pi.mul qj).add (pj.mul qi).neg))⟩

theorem plaquette_eq_word (extent : Nat) (face : Z4Plaq) :
    PolyQuaternionCoeffEqv (correctedSlabPlaquettePolynomial extent face)
      (plaquetteWord (correctedSlabLinkPolynomial extent (faceLinkA face))
        (correctedSlabLinkPolynomial extent (faceLinkB face))
        (correctedSlabLinkPolynomial extent (faceLinkC face))
        (correctedSlabLinkPolynomial extent (faceLinkD face))) :=
  (((PolyQuaternionCoeffEqv.one_mul _).mul (PolyQuaternionCoeffEqv.refl _)).mul
    (PolyQuaternionCoeffEqv.refl _)).mul (PolyQuaternionCoeffEqv.refl _)

theorem plaquette_reflection_word {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    QImage extent (correctedSlabPlaquettePolynomial extent face)
      (plaquetteWord (orientedReflectedLink extent (faceLinkA face))
        (orientedReflectedLink extent (faceLinkB face))
        (orientedReflectedLink extent (faceLinkC face))
        (orientedReflectedLink extent (faceLinkD face))) := by
  have hl (link : Z4Link) (hi : link ∈ edgesOf face) :=
    link_reflection ((mem_boundaryCompleteSlabLinks_iff extent link).mpr ⟨face, hf, hi⟩)
  have h := image_mul (image_mul (image_mul (image_mul (image_one extent)
    (hl (faceLinkA face) (by simp [faceLinkA, edgesOf])))
    (hl (faceLinkB face) (by simp [faceLinkB, edgesOf])))
    (image_conj (hl (faceLinkC face) (by simp [faceLinkC, edgesOf]))))
    (image_conj (hl (faceLinkD face) (by simp [faceLinkD, edgesOf])))
  exact h.trans_coeff ((((PolyQuaternionCoeffEqv.one_mul _).mul (PolyQuaternionCoeffEqv.refl _)).mul
    (PolyQuaternionCoeffEqv.refl _)).mul (PolyQuaternionCoeffEqv.refl _))

private def environment (a b c d : PolyQuaternion) : Nat → RatPoly
  | 0 => a.scalar | 1 => a.iPart | 2 => a.jPart | 3 => a.kPart
  | 4 => b.scalar | 5 => b.iPart | 6 => b.jPart | 7 => b.kPart
  | 8 => c.scalar | 9 => c.iPart | 10 => c.jPart | 11 => c.kPart
  | 12 => d.scalar | 13 => d.iPart | 14 => d.jPart | 15 => d.kPart | _ => polyZero

private def wordExpr (a b c d : PolyQuaternionExpr) : PolyQuaternionExpr :=
  .mul (.mul (.mul a b) (.conj c)) (.conj d)

/-- Scalar cyclic-inverse identity. No quaternion factors are commuted,
and no unit-norm condition is needed. The certificate has sixteen formal
variables, independent of slab extent, character degree and observable size. -/
theorem temporal_word_scalar (a b c d : PolyQuaternion) :
    RatPolyCoeffEqv (plaquetteWord c (PolyQuaternion.conj b) a (PolyQuaternion.conj d)).scalar
      (plaquetteWord a b c d).scalar :=
  coeffEvalExpr_eqv_of_normalize_eq
    (wordExpr (.coordinate 8) (.conj (.coordinate 4)) (.coordinate 0) (.conj (.coordinate 12))).scalar
    (wordExpr (.coordinate 0) (.coordinate 4) (.coordinate 8) (.coordinate 12)).scalar
    (by decide) (environment a b c d)

private abbrev FourQuaternions := PolyQuaternion × PolyQuaternion × PolyQuaternion × PolyQuaternion

private def sourceFour (u : Z4Link → PolyQuaternion) (extent : Nat) (face : Z4Plaq) : FourQuaternions :=
  (orientedFor u extent (faceLinkA face), orientedFor u extent (faceLinkB face),
    orientedFor u extent (faceLinkC face), orientedFor u extent (faceLinkD face))

private def targetFour (u : Z4Link → PolyQuaternion) (extent : Nat) (face : Z4Plaq) : FourQuaternions :=
  let f := timeReflectPlaquette extent face
  if (dirsOf face.2).2 = .x3 then
    (u (faceLinkC f), PolyQuaternion.conj (u (faceLinkB f)), u (faceLinkA f), PolyQuaternion.conj (u (faceLinkD f)))
  else (u (faceLinkA f), u (faceLinkB f), u (faceLinkC f), u (faceLinkD f))

private theorem four_geometry (u : Z4Link → PolyQuaternion) {extent : Nat} {face : Z4Plaq}
    (ha : plaquetteTimeAdmissible extent face) : sourceFour u extent face = targetFour u extent face := by
  rcases face with ⟨⟨x, y, z, t⟩, plane⟩
  cases plane
  all_goals try rfl
  all_goals
    have ht : t < extent := ha
    have hshift : extent - (t + 1) + 1 = extent - t := by omega
    simp only [sourceFour, targetFour, faceLinkA, faceLinkB, faceLinkC, faceLinkD, dirsOf, addE,
      timeReflectPlaquette, orientedFor, timeReflectLink, hshift, reduceCtorEq, ↓reduceIte]

private def fourScalar (q : FourQuaternions) : RatPoly :=
  (plaquetteWord q.1 q.2.1 q.2.2.1 q.2.2.2).scalar

private theorem word_scalar_for (u : Z4Link → PolyQuaternion) {extent : Nat} {face : Z4Plaq}
    (ha : plaquetteTimeAdmissible extent face) :
    RatPolyCoeffEqv (fourScalar (sourceFour u extent face))
      (plaquetteWord (u (faceLinkA (timeReflectPlaquette extent face)))
        (u (faceLinkB (timeReflectPlaquette extent face)))
        (u (faceLinkC (timeReflectPlaquette extent face)))
        (u (faceLinkD (timeReflectPlaquette extent face)))).scalar := by
  rw [four_geometry u ha]
  unfold targetFour
  split
  · exact temporal_word_scalar _ _ _ _
  · exact RatPolyCoeffEqv.refl _

theorem oriented_word_scalar {extent : Nat} {face : Z4Plaq}
    (ha : plaquetteTimeAdmissible extent face) :
    RatPolyCoeffEqv (plaquetteWord (orientedReflectedLink extent (faceLinkA face))
      (orientedReflectedLink extent (faceLinkB face))
      (orientedReflectedLink extent (faceLinkC face))
      (orientedReflectedLink extent (faceLinkD face))).scalar
      (plaquetteWord (correctedSlabLinkPolynomial extent (faceLinkA (timeReflectPlaquette extent face)))
        (correctedSlabLinkPolynomial extent (faceLinkB (timeReflectPlaquette extent face)))
        (correctedSlabLinkPolynomial extent (faceLinkC (timeReflectPlaquette extent face)))
        (correctedSlabLinkPolynomial extent (faceLinkD (timeReflectPlaquette extent face)))).scalar :=
  word_scalar_for (correctedSlabLinkPolynomial extent) ha

/-- Actual oriented plaquette scalar reflection on the literal common
carrier. Spatial and temporal faces, every extent, no finite face scan. -/
theorem plaquette_scalar_reflection {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    ReflectionImage extent (correctedSlabPlaquettePolynomial extent face).scalar
      (correctedSlabPlaquettePolynomial extent (timeReflectPlaquette extent face)).scalar :=
  (show PaddedPolynomialCoeffEqv _ _ _ from (plaquette_reflection_word hf).scalar).trans
    (.of_coeff ((oriented_word_scalar ((mem_boundaryCompleteSlabPlaquettes extent face).mp hf).2).trans
      (plaquette_eq_word extent (timeReflectPlaquette extent face)).scalar.symm))

theorem plaquette_character_reflection {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) (spin : Nat) :
    ReflectionImage extent (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin)
      (characterPolynomial (correctedSlabPlaquettePolynomial extent (timeReflectPlaquette extent face)).scalar spin) :=
  (PaddedPolynomialCoeffEqv.of_prefix (reflectCorrectedSlabPolynomial_character_prefix extent _ spin)).trans
    ((plaquette_scalar_reflection hf).character spin)

end YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection.time_coordinate_reflection_prefix
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection.time_link_reflection
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection.orientedReflectedLink
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection.link_reflection
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection.plaquette_eq_word
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection.plaquette_reflection_word
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection.temporal_word_scalar
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection.oriented_word_scalar
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection.plaquette_scalar_reflection
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection.plaquette_character_reflection
