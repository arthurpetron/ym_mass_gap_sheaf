/-
# Exact link support of ORIGINAL heat factors and selected remainders

Locality is checked at quaternion-block level, using each original ordered
plaquette's four literal links. It is preserved by the character recurrence,
finite heat sums and shared-link products. Disjoint link lists therefore
give the existing disjoint-block Haar hypothesis, without an independence
axiom. These statements do not assert that a full interacting slab splits.
-/

import YMGap.Continuum.BF4ExactSlabRemainderExpansion
import YMGap.Continuum.BF4ExactSlabLowerChannelLocality

namespace YMGap.Continuum.BF4ExactSlabFaceLinkLocality

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactSlabRemainderExpansion
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization

def faceLinks (extent : Nat) (ids : List Nat) : List Z4Link :=
  ids.flatMap (fun id => edgesOf (slabPlaquetteAt extent id))

def LinkLocal (extent : Nat) (links : List Z4Link) (p : RatPoly) : Prop :=
  BlockLocal (boundaryCompleteSlabLinks extent).length
    (fun block => correctedSlabLinkAt extent block ∈ links) p

def LinksDisjoint (left right : List Z4Link) : Prop :=
  ∀ link, link ∈ left → link ∈ right → False

theorem LinkLocal.mono {extent : Nat} {left right : List Z4Link} {p : RatPoly}
    (hp : LinkLocal extent left p) (h : ∀ link, link ∈ left → link ∈ right) : LinkLocal extent right p :=
  fun t ht block hb hn => hp t ht block hb (fun hl => hn (h _ hl))

theorem linkLocal_disjoint {extent : Nat} {left right : List Z4Link} {p q : RatPoly}
    (hp : LinkLocal extent left p) (hq : LinkLocal extent right q) (hd : LinksDisjoint left right) :
    BlockDisjoint (boundaryCompleteSlabLinks extent).length p q := by
  intro s hs t ht block hb
  by_cases hl : correctedSlabLinkAt extent block ∈ left
  · exact Or.inr (hq t ht block hb (fun hr => hd _ hl hr))
  · exact Or.inl (hp s hs block hb hl)

private structure LocalQuaternion (extent : Nat) (links : List Z4Link) (p : PolyQuaternion) : Prop where
  scalar : LinkLocal extent links p.scalar
  iPart : LinkLocal extent links p.iPart
  jPart : LinkLocal extent links p.jPart
  kPart : LinkLocal extent links p.kPart

private theorem quaternion_one (extent : Nat) (links : List Z4Link) : LocalQuaternion extent links PolyQuaternion.one :=
  ⟨BlockLocal.one _ _, BlockLocal.zero _ _, BlockLocal.zero _ _, BlockLocal.zero _ _⟩

private theorem LocalQuaternion.conj {extent : Nat} {links : List Z4Link} {p : PolyQuaternion}
    (hp : LocalQuaternion extent links p) : LocalQuaternion extent links (PolyQuaternion.conj p) :=
  ⟨hp.scalar, hp.iPart.neg, hp.jPart.neg, hp.kPart.neg⟩

private theorem LocalQuaternion.mul {extent : Nat} {links : List Z4Link} {p q : PolyQuaternion}
    (hp : LocalQuaternion extent links p) (hq : LocalQuaternion extent links q) :
    LocalQuaternion extent links (PolyQuaternion.mul p q) := by
  constructor <;> simp only [PolyQuaternion.mul]
  all_goals repeat' first
    | exact hp.scalar | exact hp.iPart | exact hp.jPart | exact hp.kPart
    | exact hq.scalar | exact hq.iPart | exact hq.jPart | exact hq.kPart
    | apply BlockLocal.add | apply BlockLocal.neg | apply BlockLocal.mul

private theorem quaternion_link (extent : Nat) (links : List Z4Link) {link : Z4Link} (hl : link ∈ links) :
    LocalQuaternion extent links (correctedSlabLinkPolynomial extent link) := by
  by_cases hm : link ∈ boundaryCompleteSlabLinks extent
  · have hc (c : Nat) (h : c < 4) : LinkLocal extent links
        (polyVar (4*(boundaryCompleteSlabLinks extent).idxOf link+c)) := by
      apply BlockLocal.coordinate
      rw [show (4*(boundaryCompleteSlabLinks extent).idxOf link+c)/4 =
        (boundaryCompleteSlabLinks extent).idxOf link by omega, correctedSlabLinkAt_idxOf hm]
      exact hl
    rw [correctedSlabLinkPolynomial_of_mem hm]
    exact ⟨hc 0 (by omega), hc 1 (by omega), hc 2 (by omega), hc 3 (by omega)⟩
  · rw [correctedSlabLinkPolynomial_of_not_mem hm]
    exact quaternion_one extent links

theorem face_scalar_local (extent : Nat) (face : Z4Plaq) :
    LinkLocal extent (edgesOf face) (correctedSlabPlaquettePolynomial extent face).scalar := by
  have h := (((((quaternion_one extent (edgesOf face)).mul
    (quaternion_link extent _ (show faceLinkA face ∈ edgesOf face by simp [faceLinkA, edgesOf]))).mul
    (quaternion_link extent _ (show faceLinkB face ∈ edgesOf face by simp [faceLinkB, edgesOf]))).mul
    (quaternion_link extent _ (show faceLinkC face ∈ edgesOf face by simp [faceLinkC, edgesOf])).conj).mul
    (quaternion_link extent _ (show faceLinkD face ∈ edgesOf face by simp [faceLinkD, edgesOf])).conj)
  exact h.scalar

theorem heatFace_local (w : Q') (K extent id : Nat) :
    LinkLocal extent (edgesOf (slabPlaquetteAt extent id)) (faceHeatPolynomial w K extent id) := by
  rw [faceHeatPolynomial_eq_sum]
  exact BlockLocal.finiteSum _ _ (fun spin _ => ((face_scalar_local extent _).character spin).smul _)

theorem remainderFace_local (w : Q') (K extent id : Nat) :
    LinkLocal extent (edgesOf (slabPlaquetteAt extent id)) (faceHeatTail w extent id 1 K) :=
  BlockLocal.finiteSum _ _ (fun i _ => ((face_scalar_local extent _).character (1+i)).smul _)

theorem heatProduct_local (w : Q') (K extent : Nat) (ids : List Nat) :
    LinkLocal extent (faceLinks extent ids) (polynomialProduct (faceHeatPolynomial w K extent) ids) :=
  BlockLocal.fold _ ids (fun id hi => (heatFace_local w K extent id).mono
    (fun _ hl => List.mem_flatMap.mpr ⟨id, hi, hl⟩))

theorem remainderProduct_local (w : Q') (K extent : Nat) (ids : List Nat) :
    LinkLocal extent (faceLinks extent ids) (remainderProduct w K extent ids) :=
  BlockLocal.fold _ ids (fun id hi => (remainderFace_local w K extent id).mono
    (fun _ hl => List.mem_flatMap.mpr ⟨id, hi, hl⟩))

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') : SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_sum {A : Type} {blocks : Nat} (f : A → RatPoly)
    (h : ∀ a, SupportedQuaternionBlocks blocks (f a)) : ∀ xs : List A, SupportedQuaternionBlocks blocks (finitePolySum f xs)
  | [] => fun _ ht => False.elim (List.not_mem_nil ht)
  | a :: xs => supported_add (h a) (support_sum f h xs)

private theorem support_product {A : Type} {blocks : Nat} (f : A → RatPoly)
    (h : ∀ a, SupportedQuaternionBlocks blocks (f a)) : ∀ xs : List A, SupportedQuaternionBlocks blocks (polynomialProduct f xs)
  | [] => supported_one blocks
  | a :: xs => supported_polyMul (h a) (support_product f h xs)

theorem heatFace_supported (w : Q') (K extent id : Nat) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length (faceHeatPolynomial w K extent id) := by
  rw [faceHeatPolynomial_eq_sum]
  exact support_sum _ (fun spin => support_smul (original_character_support extent _ spin) _) _

theorem remainderFace_supported (w : Q') (K extent id : Nat) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length (faceHeatTail w extent id 1 K) :=
  support_sum _ (fun i => support_smul (original_character_support extent _ (1+i)) _) _

theorem heatProduct_supported (w : Q') (K extent : Nat) (ids : List Nat) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length (polynomialProduct (faceHeatPolynomial w K extent) ids) :=
  support_product _ (heatFace_supported w K extent) ids

theorem remainderProduct_supported (w : Q') (K extent : Nat) (ids : List Nat) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length (remainderProduct w K extent ids) :=
  support_product _ (remainderFace_supported w K extent) ids

end YMGap.Continuum.BF4ExactSlabFaceLinkLocality

#print axioms YMGap.Continuum.BF4ExactSlabFaceLinkLocality.faceLinks
#print axioms YMGap.Continuum.BF4ExactSlabFaceLinkLocality.LinkLocal
#print axioms YMGap.Continuum.BF4ExactSlabFaceLinkLocality.LinksDisjoint
#print axioms YMGap.Continuum.BF4ExactSlabFaceLinkLocality.LinkLocal.mono
#print axioms YMGap.Continuum.BF4ExactSlabFaceLinkLocality.linkLocal_disjoint
#print axioms YMGap.Continuum.BF4ExactSlabFaceLinkLocality.face_scalar_local
#print axioms YMGap.Continuum.BF4ExactSlabFaceLinkLocality.heatFace_local
#print axioms YMGap.Continuum.BF4ExactSlabFaceLinkLocality.remainderFace_local
#print axioms YMGap.Continuum.BF4ExactSlabFaceLinkLocality.heatProduct_local
#print axioms YMGap.Continuum.BF4ExactSlabFaceLinkLocality.remainderProduct_local
#print axioms YMGap.Continuum.BF4ExactSlabFaceLinkLocality.heatFace_supported
#print axioms YMGap.Continuum.BF4ExactSlabFaceLinkLocality.remainderFace_supported
#print axioms YMGap.Continuum.BF4ExactSlabFaceLinkLocality.heatProduct_supported
#print axioms YMGap.Continuum.BF4ExactSlabFaceLinkLocality.remainderProduct_supported
