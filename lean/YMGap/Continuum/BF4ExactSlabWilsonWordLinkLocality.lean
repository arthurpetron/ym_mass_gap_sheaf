/-
# Link locality of an arbitrary ORIGINAL slab Wilson tail

The four coordinate polynomials of the actual ordered slab word depend only
on the underlying links displayed by that word.  Hence, if a selected
physical link is absent from the tail, all four coordinates are independent
of its quaternion block.  This is a finite polynomial-locality statement for
the original carrier, intended for later one-link Haar extraction only.
-/

import YMGap.Continuum.BF4ExactSlabFaceLinkLocality
import YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection
import YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord

namespace YMGap.Continuum.BF4ExactSlabWilsonWordLinkLocality

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter

private structure LocalQuaternion
    (extent : Nat) (links : List Z4Link) (p : PolyQuaternion) : Prop where
  scalar : LinkLocal extent links p.scalar
  iPart : LinkLocal extent links p.iPart
  jPart : LinkLocal extent links p.jPart
  kPart : LinkLocal extent links p.kPart

private theorem LocalQuaternion.one (extent : Nat) (links : List Z4Link) :
    LocalQuaternion extent links PolyQuaternion.one :=
  ⟨BlockLocal.one _ _, BlockLocal.zero _ _, BlockLocal.zero _ _, BlockLocal.zero _ _⟩

private theorem LocalQuaternion.conj {extent : Nat} {links : List Z4Link}
    {p : PolyQuaternion} (hp : LocalQuaternion extent links p) :
    LocalQuaternion extent links (PolyQuaternion.conj p) :=
  ⟨hp.scalar, hp.iPart.neg, hp.jPart.neg, hp.kPart.neg⟩

private theorem LocalQuaternion.mul {extent : Nat} {links : List Z4Link}
    {p q : PolyQuaternion} (hp : LocalQuaternion extent links p)
    (hq : LocalQuaternion extent links q) :
    LocalQuaternion extent links (PolyQuaternion.mul p q) := by
  constructor <;> simp only [PolyQuaternion.mul]
  all_goals repeat' first
    | exact hp.scalar | exact hp.iPart | exact hp.jPart | exact hp.kPart
    | exact hq.scalar | exact hq.iPart | exact hq.jPart | exact hq.kPart
    | apply BlockLocal.add | apply BlockLocal.neg | apply BlockLocal.mul

private theorem LocalQuaternion.mono {extent : Nat} {left right : List Z4Link}
    {p : PolyQuaternion} (hp : LocalQuaternion extent left p)
    (h : ∀ link, link ∈ left → link ∈ right) :
    LocalQuaternion extent right p :=
  ⟨hp.scalar.mono h, hp.iPart.mono h, hp.jPart.mono h, hp.kPart.mono h⟩

private theorem coordinateLink_local (extent : Nat) (link : Z4Link) :
    LocalQuaternion extent [link] (correctedSlabLinkPolynomial extent link) := by
  by_cases hm : link ∈ boundaryCompleteSlabLinks extent
  · have hc (c : Nat) (h : c < 4) : LinkLocal extent [link]
        (polyVar (4*(boundaryCompleteSlabLinks extent).idxOf link+c)) := by
      apply BlockLocal.coordinate
      rw [show (4*(boundaryCompleteSlabLinks extent).idxOf link+c)/4 =
        (boundaryCompleteSlabLinks extent).idxOf link by omega,
        correctedSlabLinkAt_idxOf hm]
      exact List.mem_cons_self
    rw [correctedSlabLinkPolynomial_of_mem hm]
    exact ⟨hc 0 (by omega), hc 1 (by omega), hc 2 (by omega), hc 3 (by omega)⟩
  · rw [correctedSlabLinkPolynomial_of_not_mem hm]
    exact LocalQuaternion.one extent [link]

private theorem orientedLink_local (extent : Nat) (entry : OrientedBF4Link) :
    LocalQuaternion extent [entry.link]
      (orientedCorrectedSlabLinkPolynomial extent entry) := by
  unfold orientedCorrectedSlabLinkPolynomial
  cases h : entry.reverse with
  | false => simpa only [h] using coordinateLink_local extent entry.link
  | true => simpa only [h] using (coordinateLink_local extent entry.link).conj

private theorem word_local (extent : Nat) : ∀ edges : List OrientedBF4Link,
    LocalQuaternion extent (edges.map OrientedBF4Link.link) (word extent edges)
  | [] => LocalQuaternion.one extent []
  | entry :: tail => by
      change LocalQuaternion extent (entry.link :: tail.map OrientedBF4Link.link)
        (PolyQuaternion.mul (orientedCorrectedSlabLinkPolynomial extent entry)
          (word extent tail))
      exact
        ((orientedLink_local extent entry).mono
          (fun _ h => List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h)))).mul
        ((word_local extent tail).mono
          (fun _ h => List.mem_cons_of_mem entry.link h))

/-- If the selected physical link is absent from the literal ordered tail,
all four coordinate polynomials of that ORIGINAL slab word have degree zero
in its actual quaternion block.  The existing `degree_zero_independent`
converts each packaged field to syntactic block independence for Haar
consumers. -/
theorem word_blockDegree_zero_of_link_absent
    (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent)
    (edges : List OrientedBF4Link)
    (habsent : ∀ entry, entry ∈ edges → entry.link ≠ link) :
    HasPolyQuaternionBlockDegree
      ((boundaryCompleteSlabLinks extent).idxOf link) 0 (word extent edges) := by
  have hn : link ∉ edges.map OrientedBF4Link.link := by
    intro h
    obtain ⟨entry, he, hlink⟩ := List.mem_map.mp h
    exact habsent entry he hlink
  have hlocal := word_local extent edges
  exact
    ⟨linkLocal_degree_zero hlocal.scalar link hl hn,
      linkLocal_degree_zero hlocal.iPart link hl hn,
      linkLocal_degree_zero hlocal.jPart link hl hn,
      linkLocal_degree_zero hlocal.kPart link hl hn⟩

#print axioms word_blockDegree_zero_of_link_absent

end YMGap.Continuum.BF4ExactSlabWilsonWordLinkLocality
