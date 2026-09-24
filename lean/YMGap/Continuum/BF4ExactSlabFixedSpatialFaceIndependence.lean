/-
# Literal fixed-slice heat factors omit links outside their face

Every finite heat prefix of the original ordered SliceHeat plaquette is
supported on the width-only carrier. A block absent from the literal face
edges is syntactically independent of the complete prefix, at every cutoff
and nome. The same statements hold for an arbitrary ordered face product,
including repeated faces and the empty product.

The consumer is original-action face peeling with all other factors retained.
No unique-incidence geometry, face cancellation, positivity or gap estimate is
assumed or proved here. Off-carrier links use the existing identity fallback.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
import YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
  (orientedPlaquetteBoundary_link_mem_edgesOf)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (link orientedLink plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (supported_smul)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger (idxOf_injective_on_members)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal (independent_of_local)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_one supported_add)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "N" width:arg => List.length (baseLinks width)

private structure LocalQuaternion (blocks : Nat) (allowed : Nat → Prop)
    (q : PolyQuaternion) : Prop where
  scalar : BlockLocal blocks allowed q.scalar
  iPart : BlockLocal blocks allowed q.iPart
  jPart : BlockLocal blocks allowed q.jPart
  kPart : BlockLocal blocks allowed q.kPart

private theorem local_one (blocks : Nat) (allowed : Nat → Prop) :
    LocalQuaternion blocks allowed PolyQuaternion.one :=
  ⟨BlockLocal.one _ _, BlockLocal.zero _ _, BlockLocal.zero _ _, BlockLocal.zero _ _⟩

private theorem LocalQuaternion.conj {blocks : Nat} {allowed : Nat → Prop}
    {p : PolyQuaternion} (hp : LocalQuaternion blocks allowed p) :
    LocalQuaternion blocks allowed (PolyQuaternion.conj p) :=
  ⟨hp.scalar, hp.iPart.neg, hp.jPart.neg, hp.kPart.neg⟩

private theorem LocalQuaternion.mul {blocks : Nat} {allowed : Nat → Prop}
    {p q : PolyQuaternion} (hp : LocalQuaternion blocks allowed p)
    (hq : LocalQuaternion blocks allowed q) :
    LocalQuaternion blocks allowed (PolyQuaternion.mul p q) := by
  constructor <;> simp only [PolyQuaternion.mul]
  all_goals repeat' first
    | exact hp.scalar | exact hp.iPart | exact hp.jPart | exact hp.kPart
    | exact hq.scalar | exact hq.iPart | exact hq.jPart | exact hq.kPart
    | apply BlockLocal.add | apply BlockLocal.neg | apply BlockLocal.mul

private theorem link_local (width i : Nat) (l : Z4Link)
    (hl : l ∈ baseLinks width → (baseLinks width).idxOf l ≠ i) :
    LocalQuaternion (N width) (fun b => b ≠ i) (link width l) := by
  by_cases hm : l ∈ baseLinks width
  · have hc (c : Nat) (h : c < 4) : BlockLocal (N width) (fun b => b ≠ i)
        (polyVar (4*(baseLinks width).idxOf l+c)) := by
      apply BlockLocal.coordinate
      rw [show (4*(baseLinks width).idxOf l+c)/4 = (baseLinks width).idxOf l by omega]
      exact hl hm
    rw [link, if_pos hm]
    exact ⟨hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide)⟩
  · rw [link, if_neg hm]
    exact local_one _ _

private theorem oriented_local (width i : Nat) (e : OrientedBF4Link)
    (he : e.link ∈ baseLinks width → (baseLinks width).idxOf e.link ≠ i) :
    LocalQuaternion (N width) (fun b => b ≠ i) (orientedLink width e) := by
  unfold orientedLink
  split
  · exact (link_local width i e.link he).conj
  · exact link_local width i e.link he

private theorem word_local (width i : Nat) :
    ∀ (word : List OrientedBF4Link),
    (∀ e, e ∈ word → e.link ∈ baseLinks width → (baseLinks width).idxOf e.link ≠ i) →
    ∀ p, LocalQuaternion (N width) (fun b => b ≠ i) p →
      LocalQuaternion (N width) (fun b => b ≠ i)
        (word.foldl (fun q e => PolyQuaternion.mul q (orientedLink width e)) p)
  | [], _, _, hp => hp
  | e::es, he, _, hp => word_local width i es
      (fun f hf => he f (List.mem_cons_of_mem e hf)) _
      (hp.mul (oriented_local width i e (he e List.mem_cons_self)))

private theorem heatFace_local (w : Q') (K width : Nat) (face : Z4Plaq) (i : Nat)
    (hnot : ∀ l, l ∈ edgesOf face → l ∈ baseLinks width → (baseLinks width).idxOf l ≠ i) :
    BlockLocal (N width) (fun b => b ≠ i) (heatPrefix w K (plaquette width face).scalar) := by
  have hp := word_local width i (orientedPlaquetteBoundary face)
    (fun e he => hnot e.link (orientedPlaquetteBoundary_link_mem_edgesOf he))
    PolyQuaternion.one (local_one _ _)
  exact BlockLocal.finiteSum _ _ (fun spin _ => (hp.scalar.character spin).smul _)

private theorem sum_supported {A : Type} {blocks : Nat} (f : A → RatPoly)
    (hf : ∀ a, SupportedQuaternionBlocks blocks (f a)) :
    ∀ xs : List A, SupportedQuaternionBlocks blocks (finitePolySum f xs)
  | [] => fun _ ht => False.elim (List.not_mem_nil ht)
  | a::xs => supported_add (hf a) (sum_supported f hf xs)

/-- Arbitrary faces are allowed: the original link definition supplies its
identity fallback when a face edge is outside the fixed slice. -/
theorem heatFace_supported (w : Q') (K width : Nat) (face : Z4Plaq) :
    SupportedQuaternionBlocks (N width) (heatPrefix w K (plaquette width face).scalar) := by
  apply sum_supported
  intro spin
  exact supported_smul (SU2QuaternionRelativeHeatPairGeometry.character_supported
    (plaquette_supported width (N width) (Nat.le_refl _) face).scalar spin) _

/-- Absence expressed directly in the original block indexing. -/
theorem heatFace_independent_index (w : Q') (K width : Nat) (face : Z4Plaq)
    (i : Nat) (hi : i < N width)
    (hnot : ∀ l, l ∈ edgesOf face → l ∈ baseLinks width → (baseLinks width).idxOf l ≠ i) :
    QuaternionBlockIndependent i (heatPrefix w K (plaquette width face).scalar) :=
  independent_of_local (heatFace_local w K width face i hnot) hi (fun h => h rfl)

/-- Every character of a literal face word is independent of a block omitted
by all four face edges. This is the character-level form of the same public
index guard used for the full heat prefix. -/
theorem characterFace_independent_index (width : Nat) (face : Z4Plaq)
    (i spin : Nat) (hi : i < N width)
    (hnot : ∀ l, l ∈ edgesOf face → l ∈ baseLinks width →
      (baseLinks width).idxOf l ≠ i) :
    QuaternionBlockIndependent i
      (characterPolynomial (plaquette width face).scalar spin) := by
  have hp := word_local width i (orientedPlaquetteBoundary face)
    (fun e he => hnot e.link (orientedPlaquetteBoundary_link_mem_edgesOf he))
    PolyQuaternion.one (local_one _ _)
  exact independent_of_local (hp.scalar.character spin) hi (fun h => h rfl)

/-- A literal retained link absent from the face is absent from EVERY spin
in its full heat prefix. -/
theorem heatFace_independent (w : Q') (K : Nat) {width : Nat} {l : Z4Link}
    (hl : l ∈ baseLinks width) {face : Z4Plaq} (hnot : l ∉ edgesOf face) :
    QuaternionBlockIndependent ((baseLinks width).idxOf l)
      (heatPrefix w K (plaquette width face).scalar) := by
  apply heatFace_independent_index w K width face _ (List.idxOf_lt_length_of_mem hl)
  intro m hm hmCarrier he
  have hml : m = l := idxOf_injective_on_members hmCarrier hl he
  exact hnot (hml ▸ hm)

/-- Support of the unchanged ordered heat product, with repetitions retained. -/
theorem heatProduct_supported (w : Q') (K width : Nat) : ∀ faces : List Z4Plaq,
    SupportedQuaternionBlocks (N width)
      (polynomialProduct (fun face => heatPrefix w K (plaquette width face).scalar) faces)
  | [] => supported_one _
  | face::faces => supported_polyMul (heatFace_supported w K width face)
      (heatProduct_supported w K width faces)

/-- Block-index absence simultaneously from all retained action factors. -/
theorem heatProduct_independent_index (w : Q') (K width : Nat) (faces : List Z4Plaq)
    (i : Nat) (hi : i < N width)
    (hnot : ∀ face, face ∈ faces → ∀ l, l ∈ edgesOf face →
      l ∈ baseLinks width → (baseLinks width).idxOf l ≠ i) :
    QuaternionBlockIndependent i
      (polynomialProduct (fun face => heatPrefix w K (plaquette width face).scalar) faces) :=
  independent_of_local
    (BlockLocal.fold _ faces (fun face hf => heatFace_local w K width face i (hnot face hf)))
    hi (fun h => h rfl)

/-- No factor is dropped: every face of the supplied product must omit the
selected original link. The empty product is included. -/
theorem heatProduct_independent (w : Q') (K : Nat) {width : Nat} {l : Z4Link}
    (hl : l ∈ baseLinks width) (faces : List Z4Plaq)
    (hnot : ∀ face, face ∈ faces → l ∉ edgesOf face) :
    QuaternionBlockIndependent ((baseLinks width).idxOf l)
      (polynomialProduct (fun face => heatPrefix w K (plaquette width face).scalar) faces) := by
  apply heatProduct_independent_index w K width faces _ (List.idxOf_lt_length_of_mem hl)
  intro face hf m hm hmCarrier he
  have hml : m = l := idxOf_injective_on_members hmCarrier hl he
  exact hnot face hf (hml ▸ hm)

#print axioms heatFace_supported
#print axioms heatFace_independent_index
#print axioms characterFace_independent_index
#print axioms heatFace_independent
#print axioms heatProduct_supported
#print axioms heatProduct_independent_index
#print axioms heatProduct_independent

end YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
