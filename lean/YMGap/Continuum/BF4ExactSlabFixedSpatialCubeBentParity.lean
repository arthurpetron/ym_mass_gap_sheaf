/-
# Literal six-face subset parity for the original bent cube observable

The finite witness computation sees only the six original cube faces and
twelve physical links.  Every subset except the third face alone and its
literal five-face complement has an odd link in P*F times its selected
fundamental characters.  Exact block degree and selected-block Fubini then
annihilate that insertion in the ORIGINAL slice Haar integral.

No ambient polynomial is evaluated by the finite checker.  This is not a
character-basis completeness statement, a numerical surviving moment, an
interacting gain sign, or a completed/scaling estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree
import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
import YMGap.Continuum.FinitePolynomialSubsetExpansion

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentParity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
  (spatialFaces spatialFaces_mem_iff)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger (idxOf_injective_on_members)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion
  (firstFaceTrace thirdFaceTrace)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
  (characterFace_independent_index)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.FinitePolynomialSubsetExpansion (selections selected_mem)
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry (occurrenceCount)
open YMGap.Continuum.Z4UnitCubeIncidenceParity (faceIncidenceCount)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
  (SupportedQuaternionBlocks quaternionBlockDegree)
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord (wordAt)
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
  (orientedCoordinateQuaternion orientedCoordinateQuaternion_blockDegree)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
  (independent_has_degree_zero)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold (blockDegree_reindex)
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_one)

local notation "N" => List.length (baseLinks 2)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks bentObservable firstFaceTrace

/-- The third original cube face is the one shared with P in the bent loop. -/
def singletonSelection : List Z4Plaq := [((0,0,0,0),.p02)]

/-- Literal original face order, omitting only that third face. -/
def complementSelection : List Z4Plaq :=
  [((0,0,0,0),.p01), ((0,0,1,0),.p01),
   ((0,1,0,0),.p02), ((0,0,0,0),.p12), ((1,0,0,0),.p12)]

def selectedFaceProduct (fs : List Z4Plaq) : RatPoly :=
  polynomialProduct (fun face => characterPolynomial (plaquette 2 face).scalar 1) fs

/-- P and F are the actual first face and bent source, before Haar evaluation. -/
def selectedBentInsertion (fs : List Z4Plaq) : RatPoly :=
  polyMul (polyMul firstFaceTrace bentObservable) (selectedFaceProduct fs)

def selectionDegree (link : Z4Link) (fs : List Z4Plaq) : Nat :=
  (if link ∈ edgesOf ((0,0,0,0),.p01) then 1 else 0) +
    occurrenceCount link (bentEdges.map OrientedBF4Link.link) +
    faceIncidenceCount link fs

private def searchOddEdge (fs : List Z4Plaq) : List Z4Link → Z4Link
  | [] => ((0,0,0,0),.x0)
  | link :: rest =>
      if selectionDegree link fs % 2 = 1 then link else searchOddEdge fs rest

/-- Computed physical witness; its correctness is checked on the actual subsets. -/
def oddSelectionEdge (fs : List Z4Plaq) : Z4Link := searchOddEdge fs cubeLinks

/-- Only finite geometry is reduced here, not `baseLinks` or a Haar polynomial. -/
theorem cubeSelections_parity_checked :
    (selections cubeFaces).all (fun fs => decide
      (fs = singletonSelection ∨ fs = complementSelection ∨
        (oddSelectionEdge fs ∈ cubeLinks ∧
          selectionDegree (oddSelectionEdge fs) fs % 2 = 1))) = true := by
  decide

/-- The witness remains Type-level data; the theorem supplies its actual incidence law. -/
theorem badSelection_oddEdge (fs : List Z4Plaq) (hfs : fs ∈ selections cubeFaces)
    (hsingle : fs ≠ singletonSelection) (hcomplement : fs ≠ complementSelection) :
    oddSelectionEdge fs ∈ cubeLinks ∧
      selectionDegree (oddSelectionEdge fs) fs % 2 = 1 := by
  have h := of_decide_eq_true (List.all_eq_true.mp cubeSelections_parity_checked fs hfs)
  rcases h with h | h | h
  · exact False.elim (hsingle h)
  · exact False.elim (hcomplement h)
  · exact h

private theorem cubeFace_spatial (face : Z4Plaq) (hf : face ∈ cubeFaces) :
    face ∈ spatialFaces 2 := by
  apply (spatialFaces_mem_iff 2 face).mpr
  simp only [cubeFaces, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem bentEdge_carrier (e : OrientedBF4Link) (he : e ∈ bentEdges) :
    e.link ∈ baseLinks 2 := by
  apply cubeLinks_in_carrier
  simp only [bentEdges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem entry_degree (link : Z4Link) (hl : link ∈ baseLinks 2)
    (entry : OrientedBF4Link) (he : entry.link ∈ baseLinks 2) :
    HasPolyQuaternionBlockDegree ((baseLinks 2).idxOf link)
      (if entry.link = link then 1 else 0)
      (orientedCoordinateQuaternion ((baseLinks 2).idxOf entry.link) entry.reverse) := by
  have h := orientedCoordinateQuaternion_blockDegree
    ((baseLinks 2).idxOf entry.link) ((baseLinks 2).idxOf link) entry.reverse
  by_cases hh : entry.link = link
  · simpa only [hh, if_pos rfl] using h
  · have hi : (baseLinks 2).idxOf link ≠ (baseLinks 2).idxOf entry.link := by
      intro hi
      exact hh (idxOf_injective_on_members hl he hi).symm
    simpa only [if_neg hh, if_neg hi] using h

private theorem word_degree (link : Z4Link) (hl : link ∈ baseLinks 2) :
    ∀ es : List OrientedBF4Link,
    (∀ e, e ∈ es → e.link ∈ baseLinks 2) →
    HasPolyQuaternionBlockDegree ((baseLinks 2).idxOf link)
      (occurrenceCount link (es.map OrientedBF4Link.link))
      (wordAt (fun e => (baseLinks 2).idxOf e.link) es)
  | [], _ => ⟨hasQuaternionBlockDegree_one _, hasQuaternionBlockDegree_zero _ 0,
      hasQuaternionBlockDegree_zero _ 0, hasQuaternionBlockDegree_zero _ 0⟩
  | e :: es, hp => by
      have he := entry_degree link hl e (hp e List.mem_cons_self)
      have ht := word_degree link hl es (fun f hf => hp f (List.mem_cons_of_mem e hf))
      simpa only [List.map_cons, occurrenceCount] using he.mul ht

private theorem bent_degree (link : Z4Link) (hl : link ∈ baseLinks 2) :
    HasQuaternionBlockDegree ((baseLinks 2).idxOf link)
      (occurrenceCount link (bentEdges.map OrientedBF4Link.link)) bentObservable := by
  unfold bentObservable
  simpa only [characterPolynomial] using
    (word_degree link hl bentEdges bentEdge_carrier).scalar.smul 2

private theorem face_degree (link : Z4Link) (hl : link ∈ baseLinks 2)
    (face : Z4Plaq) (hf : face ∈ spatialFaces 2) :
    HasQuaternionBlockDegree ((baseLinks 2).idxOf link)
      (if link ∈ edgesOf face then 1 else 0)
      (characterPolynomial (plaquette 2 face).scalar 1) := by
  by_cases hh : link ∈ edgesOf face
  · rw [if_pos hh]
    exact plaquette_character_degree 2 hf hh
  · rw [if_neg hh]
    apply independent_has_degree_zero
    apply characterFace_independent_index 2 face _ 1 (List.idxOf_lt_length_of_mem hl)
    intro other ho hm he
    have hx : other = link := idxOf_injective_on_members hm hl he
    exact hh (hx ▸ ho)

attribute [local irreducible] plaquette characterPolynomial

private theorem product_degree (link : Z4Link) (hl : link ∈ baseLinks 2) :
    ∀ fs : List Z4Plaq, (∀ face, face ∈ fs → face ∈ spatialFaces 2) →
    HasQuaternionBlockDegree ((baseLinks 2).idxOf link)
      (faceIncidenceCount link fs) (selectedFaceProduct fs)
  | [], _ => by
      unfold selectedFaceProduct polynomialProduct
      exact hasQuaternionBlockDegree_one _
  | face :: fs, hp => by
      have he := face_degree link hl face (hp face List.mem_cons_self)
      have ht := product_degree link hl fs
        (fun f hf => hp f (List.mem_cons_of_mem face hf))
      unfold selectedFaceProduct at ht ⊢
      change HasQuaternionBlockDegree ((baseLinks 2).idxOf link)
        ((if link ∈ edgesOf face then 1 else 0) + faceIncidenceCount link fs)
        (polyMul (characterPolynomial (plaquette 2 face).scalar 1)
          (polynomialProduct
            (fun face => characterPolynomial (plaquette 2 face).scalar 1) fs))
      exact he.mul ht

/-- Exact original block degree, not just an upper degree bound. -/
theorem selectedBentInsertion_degree (fs : List Z4Plaq)
    (hfs : fs ∈ selections cubeFaces) (link : Z4Link) (hl : link ∈ cubeLinks) :
    HasQuaternionBlockDegree ((baseLinks 2).idxOf link)
      (selectionDegree link fs) (selectedBentInsertion fs) := by
  have hm := cubeLinks_in_carrier link hl
  have hp := face_degree link hm ((0,0,0,0),.p01)
    (cubeFace_spatial _ (by decide))
  have hp' : HasQuaternionBlockDegree ((baseLinks 2).idxOf link)
      (if link ∈ edgesOf ((0,0,0,0),.p01) then 1 else 0) firstFaceTrace := by
    unfold firstFaceTrace
    exact hp
  have hb := bent_degree link hm
  have hs := product_degree link hm fs
    (fun face hf => cubeFace_spatial face (selected_mem hfs face hf))
  unfold selectedBentInsertion selectionDegree
  exact (hp'.mul hb).mul hs

private theorem face_supported (face : Z4Plaq) :
    SupportedQuaternionBlocks N (characterPolynomial (plaquette 2 face).scalar 1) :=
  character_supported (plaquette_supported 2 N (Nat.le_refl _) face).scalar 1

private theorem product_supported : ∀ fs : List Z4Plaq,
    SupportedQuaternionBlocks N (selectedFaceProduct fs)
  | [] => by
      unfold selectedFaceProduct polynomialProduct
      exact supported_one _
  | face :: fs => by
      have ht := product_supported fs
      unfold selectedFaceProduct at ht ⊢
      change SupportedQuaternionBlocks N
        (polyMul (characterPolynomial (plaquette 2 face).scalar 1)
          (polynomialProduct
            (fun face => characterPolynomial (plaquette 2 face).scalar 1) fs))
      exact supported_polyMul (face_supported face) ht

theorem selectedBentInsertion_supported (fs : List Z4Plaq) :
    SupportedQuaternionBlocks N (selectedBentInsertion fs) := by
  have hp : SupportedQuaternionBlocks N firstFaceTrace := by
    unfold firstFaceTrace
    exact face_supported ((0,0,0,0),.p01)
  unfold selectedBentInsertion
  exact supported_polyMul
    (supported_polyMul hp bentObservable_supported)
    (product_supported fs)

private theorem haar_zero_of_odd_degree {blocks selected degree : Nat}
    (hi : selected < blocks) (p : RatPoly) (hp : SupportedQuaternionBlocks blocks p)
    (hd : HasQuaternionBlockDegree selected degree p) (ho : degree % 2 = 1) :
    quaternionHaar blocks p ≈ 0 := by
  have hn : blocks - 1 + 1 = blocks := by omega
  have hi' : selected < blocks - 1 + 1 := by omega
  let swap := headSwapBlockInvolution (blocks - 1 + 1) selected hi'
  have hhead : HasQuaternionBlockDegree 0 degree (reindexQuaternionPolynomial swap p) :=
    blockDegree_reindex swap (by omega)
      (headSwapBlockInvolution_map_zero _ _ _) hd
  have hodd : HeadQuaternionOdd (reindexQuaternionPolynomial swap p) := by
    intro term ht
    change quaternionBlockDegree term.1 0 % 2 = 1
    rw [hhead term ht, ho]
  have hf := quaternionHaar_eq_partialHaar_selected (blocks - 1) selected hi' p
    (by simpa only [hn] using hp)
  have hz := quaternionHaar_partialHaarHead_eq_zero_of_odd (blocks - 1) _ hodd
  exact Q'.eqv_trans _ _ _ (by simpa only [hn] using hf) hz

/-- Every bad literal subset vanishes on the unchanged ORIGINAL slice carrier. -/
theorem badSelection_haar_zero (fs : List Z4Plaq) (hfs : fs ∈ selections cubeFaces)
    (hsingle : fs ≠ singletonSelection) (hcomplement : fs ≠ complementSelection) :
    quaternionHaar N (selectedBentInsertion fs) ≈ 0 := by
  have he := badSelection_oddEdge fs hfs hsingle hcomplement
  exact haar_zero_of_odd_degree
    (List.idxOf_lt_length_of_mem (cubeLinks_in_carrier _ he.1)) _
    (selectedBentInsertion_supported fs)
    (selectedBentInsertion_degree fs hfs _ he.1) he.2

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentParity

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentParity.singletonSelection
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentParity.complementSelection
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentParity.selectedFaceProduct
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentParity.selectedBentInsertion
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentParity.selectionDegree
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentParity.oddSelectionEdge
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentParity.cubeSelections_parity_checked
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentParity.badSelection_oddEdge
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentParity.selectedBentInsertion_degree
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentParity.selectedBentInsertion_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentParity.badSelection_haar_zero
