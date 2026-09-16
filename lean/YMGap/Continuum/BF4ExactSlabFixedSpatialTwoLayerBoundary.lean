/-
# The original glued kernel has only fixed-width endpoint variables

The two kinetic layers and the single middle spatial heat are the actual
polynomials of `BF4ExactSlabFixedSpatialTwoLayerGluing`. Integrating the
middle schedule leaves only spatial links on the two endpoint slices,
with each spatial base coordinate at most `width`. The bound does not
grow with the ambient extent, the start time, or the heat cutoff.

This is syntactic locality and carrier support of the computed polynomial,
not yet a recoding onto one stationary carrier or a contraction estimate.
The box is an overestimate of the selected face-edge support, not a claim
that the spatial-base-cutoff action has a vertex-closed cubical boundary.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSpatialSliceFactors
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

/-- A fixed spatial box of spatial links, on one named time slice. -/
def SliceLink (width time : Nat) (link : Z4Link) : Prop :=
  link.2 ≠ .x3 ∧ link.1.1 ≤ width ∧ link.1.2.1 ≤ width ∧
    link.1.2.2.1 ≤ width ∧ link.1.2.2.2 = time

/-- Exactly two time slices; the spatial bound is independent of the ambient slab. -/
def BoundaryLink (width start : Nat) (link : Z4Link) : Prop :=
  SliceLink width start link ∨ SliceLink width (start+2) link

private theorem local_mono {nblocks : Nat} {P Q : Nat → Prop} {p : RatPoly}
    (hp : BlockLocal nblocks P p) (h : ∀ b, P b → Q b) :
    BlockLocal nblocks Q p :=
  fun t ht b hb hn => hp t ht b hb (fun ha => hn (h _ ha))

private structure LocalQuaternion (extent : Nat) (P : Z4Link → Prop) (p : PolyQuaternion) : Prop where
  scalar : BlockLocal (blocks extent) (fun b => P (correctedSlabLinkAt extent b)) p.scalar
  iPart : BlockLocal (blocks extent) (fun b => P (correctedSlabLinkAt extent b)) p.iPart
  jPart : BlockLocal (blocks extent) (fun b => P (correctedSlabLinkAt extent b)) p.jPart
  kPart : BlockLocal (blocks extent) (fun b => P (correctedSlabLinkAt extent b)) p.kPart

private theorem quaternion_one (extent : Nat) (P : Z4Link → Prop) :
    LocalQuaternion extent P PolyQuaternion.one :=
  ⟨BlockLocal.one _ _, BlockLocal.zero _ _, BlockLocal.zero _ _, BlockLocal.zero _ _⟩

private theorem LocalQuaternion.conj {extent : Nat} {P : Z4Link → Prop} {p : PolyQuaternion}
    (h : LocalQuaternion extent P p) : LocalQuaternion extent P (PolyQuaternion.conj p) :=
  ⟨h.scalar, h.iPart.neg, h.jPart.neg, h.kPart.neg⟩

private theorem LocalQuaternion.mul {extent : Nat} {P : Z4Link → Prop} {p q : PolyQuaternion}
    (hp : LocalQuaternion extent P p) (hq : LocalQuaternion extent P q) :
    LocalQuaternion extent P (PolyQuaternion.mul p q) := by
  constructor <;> simp only [PolyQuaternion.mul]
  all_goals repeat' first
    | exact hp.scalar | exact hp.iPart | exact hp.jPart | exact hp.kPart
    | exact hq.scalar | exact hq.iPart | exact hq.jPart | exact hq.kPart
    | apply BlockLocal.add | apply BlockLocal.neg | apply BlockLocal.mul

private theorem link_local {extent : Nat} {P : Z4Link → Prop} {link : Z4Link} (hl : P link) :
    LocalQuaternion extent P (correctedSlabLinkPolynomial extent link) := by
  by_cases hm : link ∈ boundaryCompleteSlabLinks extent
  · have hc (c : Nat) (h : c < 4) : BlockLocal (blocks extent)
        (fun b => P (correctedSlabLinkAt extent b))
        (polyVar (4*(boundaryCompleteSlabLinks extent).idxOf link+c)) := by
      apply BlockLocal.coordinate
      rw [show (4*(boundaryCompleteSlabLinks extent).idxOf link+c)/4 =
        (boundaryCompleteSlabLinks extent).idxOf link by omega, correctedSlabLinkAt_idxOf hm]
      exact hl
    rw [correctedSlabLinkPolynomial_of_mem hm]
    exact ⟨hc 0 (by omega), hc 1 (by omega), hc 2 (by omega), hc 3 (by omega)⟩
  · rw [correctedSlabLinkPolynomial_of_not_mem hm]
    exact quaternion_one extent P

private theorem face_edge_box {width : Nat} {face : Z4Plaq}
    (hx : face.1.1 < width) (hy : face.1.2.1 < width) (hz : face.1.2.2.1 < width)
    {link : Z4Link} (hl : link ∈ edgesOf face) :
    link.1.1 ≤ width ∧ link.1.2.1 ≤ width ∧ link.1.2.2.1 ≤ width := by
  rcases face with ⟨⟨x,y,z,t⟩,plane⟩
  cases plane <;> simp only [edgesOf, dirsOf, addE, List.mem_cons, List.not_mem_nil, or_false] at hl
  all_goals rcases hl with rfl | rfl | rfl | rfl
  all_goals dsimp only at hx hy hz ⊢
  all_goals exact ⟨by omega, by omega, by omega⟩

/-- Every original spatial heat variable lies in the fixed spatial box. -/
theorem spatialHeat_local (w : Q') (K extent width time : Nat) :
    BlockLocal (blocks extent) (fun b => SliceLink width time (correctedSlabLinkAt extent b))
      (spatialHeat w K extent width time) := by
  apply local_mono (heatProduct_local w K extent (spatialIds extent width time))
  intro b hl
  obtain ⟨id,hi,he⟩ := List.mem_flatMap.mp hl
  obtain ⟨_,hx,hy,hz,ht,hsp⟩ := (spatialIds_mem_iff extent width time id).mp hi
  have h := spatial_face_edge _ hsp _ he
  have hb := face_edge_box hx hy hz he
  exact ⟨h.1,hb.1,hb.2.1,hb.2.2,h.2.trans ht⟩

private theorem temporal_endpoints {width time : Nat} {face : Z4Plaq}
    (hx : face.1.1 < width) (hy : face.1.2.1 < width) (hz : face.1.2.2.1 < width)
    (ht : face.1.2.2.2 = time) (hd : (dirsOf face.2).2 = .x3) :
    SliceLink width time (faceLinkA face) ∧ SliceLink width (time+1) (faceLinkC face) := by
  rcases face with ⟨⟨x,y,z,t⟩,plane⟩
  cases plane <;> simp only [dirsOf] at hd <;> try cases hd
  all_goals dsimp only at hx hy hz ht
  all_goals constructor
  all_goals simp only [SliceLink, faceLinkA, faceLinkC, dirsOf, addE]
  all_goals refine ⟨(by intro h; cases h), ?_, ?_, ?_, ?_⟩ <;> omega

set_option maxHeartbeats 1000000 in
/-- The swept kinetic layer uses only spatial variables on consecutive slices. -/
theorem kineticHeat_local (w : Q') (K extent width time : Nat) :
    BlockLocal (blocks extent) (fun b =>
      SliceLink width time (correctedSlabLinkAt extent b) ∨
      SliceLink width (time+1) (correctedSlabLinkAt extent b))
      (kineticHeat w K extent width time) := by
  apply BlockLocal.fold
  intro f hf
  obtain ⟨id,hi,rfl⟩ := List.mem_map.mp hf
  obtain ⟨_,hx,hy,hz,ht,hd⟩ := (temporalIds_mem_iff extent width time id).mp hi
  have he := temporal_endpoints hx hy hz ht hd
  have ha := link_local (extent := extent) (P := fun link =>
    SliceLink width time link ∨ SliceLink width (time+1) link) (Or.inl he.1)
  have hc := link_local (extent := extent) (P := fun link =>
    SliceLink width time link ∨ SliceLink width (time+1) link) (Or.inr he.2)
  apply BlockLocal.finiteSum
  intro term _
  exact ((ha.mul hc.conj).scalar.character term.1).smul term.2

theorem middleIntegrand_local (w : Q') (K extent width start : Nat) :
    BlockLocal (blocks extent) (fun b =>
      BoundaryLink width start (correctedSlabLinkAt extent b) ∨
      SliceLink width (start+1) (correctedSlabLinkAt extent b))
      (middleIntegrand w K extent width start) := by
  apply BlockLocal.mul
  · exact local_mono (kineticHeat_local w K extent width start)
      (fun _ h => h.elim (fun h => Or.inl (Or.inl h)) Or.inr)
  · apply BlockLocal.mul
    · exact local_mono (spatialHeat_local w K extent width (start+1)) (fun _ => Or.inr)
    · exact local_mono (kineticHeat_local w K extent width (start+1))
        (fun _ h => h.elim Or.inr (fun h => Or.inl (Or.inr h)))

/-- The computed original middle integral has no temporal, middle-slice,
or spatially out-of-box variables. No positivity or physical-face guard is used. -/
theorem gluedMiddle_local (w : Q') (K extent width start : Nat) :
    BlockLocal (blocks extent) (fun b => BoundaryLink width start (correctedSlabLinkAt extent b))
      (gluedMiddle w K extent width start) := by
  have h := integrateBlocks_local (middleSchedule extent start)
    (middleIntegrand_local w K extent width start)
  intro term ht b hb hn
  apply h term ht b hb
  intro ha
  rcases ha.1 with he | hm
  · exact hn he
  · exact ha.2 (List.mem_filter.mpr ⟨List.mem_range.mpr hb,
      decide_eq_true ⟨hm.1,hm.2.2.2.2⟩⟩)

theorem kineticHeat_supported (w : Q') (K extent width time : Nat) :
    SupportedQuaternionBlocks (blocks extent) (kineticHeat w K extent width time) :=
  product_supported _ (relative_character_supported extent) _

theorem middleIntegrand_supported (w : Q') (K extent width start : Nat) :
    SupportedQuaternionBlocks (blocks extent) (middleIntegrand w K extent width start) :=
  supported_polyMul (kineticHeat_supported w K extent width start)
    (supported_polyMul (heatProduct_supported w K extent _)
      (kineticHeat_supported w K extent width (start+1)))

/-- Ambient support is preserved as well as locality; there is no unchecked
out-of-carrier tail that could obstruct exact boundary compression. -/
theorem gluedMiddle_supported (w : Q') (K extent width start : Nat) :
    SupportedQuaternionBlocks (blocks extent) (gluedMiddle w K extent width start) :=
  integrateBlocks_supported _ (middleIntegrand_supported w K extent width start)

end YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary.SliceLink
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary.BoundaryLink
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary.spatialHeat_local
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary.kineticHeat_local
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary.middleIntegrand_local
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary.gluedMiddle_local
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary.kineticHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary.middleIntegrand_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary.gluedMiddle_supported
