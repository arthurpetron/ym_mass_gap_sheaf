/-
# Original cube-face channel parity with the P-only insertion

On the literal six-face selection list, P times the selected fundamental
characters has a computed odd physical edge unless the selection is P alone
or its five-face complement. Exact original block degree, support and
selected-block Fubini prove vanishing on the unchanged slice Haar carrier.
The checker reduces only finite face/link incidence, not ambient indices or
polynomials. No surviving moment value, action normalization, transfer range,
gain sign, completed estimate or scaling conclusion is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentParity

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumParity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
  (spatialFaces spatialFaces_mem_iff)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger (idxOf_injective_on_members)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
  (cubeFaces cubeLinks cubeLinks_in_carrier)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion (firstFaceTrace)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentParity (selectedFaceProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree (plaquette_character_degree)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
  (characterFace_independent_index)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.FinitePolynomialSubsetExpansion (selections selected_mem)
open YMGap.Continuum.Z4UnitCubeIncidenceParity (faceIncidenceCount)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
  (SupportedQuaternionBlocks quaternionBlockDegree)
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
  (independent_has_degree_zero)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold (blockDegree_reindex)
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_one)

local notation "N" => List.length (baseLinks 2)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks firstFaceTrace

def singletonSelection : List Z4Plaq := [((0,0,0,0),.p01)]

def complementSelection : List Z4Plaq :=
  [((0,0,1,0),.p01), ((0,0,0,0),.p02), ((0,1,0,0),.p02),
   ((0,0,0,0),.p12), ((1,0,0,0),.p12)]

/-- The shared original selected-face product retains its literal order. -/
def selectedVacuumInsertion (fs : List Z4Plaq) : RatPoly :=
  polyMul firstFaceTrace (selectedFaceProduct fs)

def vacuumSelectionDegree (link : Z4Link) (fs : List Z4Plaq) : Nat :=
  (if link ∈ edgesOf ((0,0,0,0),.p01) then 1 else 0) + faceIncidenceCount link fs

private def searchVacuumOddEdge (fs : List Z4Plaq) : List Z4Link → Z4Link
  | [] => ((0,0,0,0),.x0)
  | link :: rest =>
      if vacuumSelectionDegree link fs % 2 = 1 then link else searchVacuumOddEdge fs rest

/-- A computed physical edge, not a witness chosen from a propositional existence. -/
def vacuumOddEdge (fs : List Z4Plaq) : Z4Link := searchVacuumOddEdge fs cubeLinks

theorem cubeVacuumSelections_parity_checked :
    (selections cubeFaces).all (fun fs => decide
      (fs = singletonSelection ∨ fs = complementSelection ∨
        (vacuumOddEdge fs ∈ cubeLinks ∧
          vacuumSelectionDegree (vacuumOddEdge fs) fs % 2 = 1))) = true := by
  decide

theorem badVacuumSelection_oddEdge (fs : List Z4Plaq)
    (hfs : fs ∈ selections cubeFaces)
    (hsingle : fs ≠ singletonSelection)
    (hcomplement : fs ≠ complementSelection) :
    vacuumOddEdge fs ∈ cubeLinks ∧
      vacuumSelectionDegree (vacuumOddEdge fs) fs % 2 = 1 := by
  have h := of_decide_eq_true
    (List.all_eq_true.mp cubeVacuumSelections_parity_checked fs hfs)
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

theorem selectedVacuumInsertion_degree (fs : List Z4Plaq)
    (hfs : fs ∈ selections cubeFaces) (link : Z4Link) (hl : link ∈ cubeLinks) :
    HasQuaternionBlockDegree ((baseLinks 2).idxOf link)
      (vacuumSelectionDegree link fs) (selectedVacuumInsertion fs) := by
  have hm := cubeLinks_in_carrier link hl
  have hp := face_degree link hm ((0,0,0,0),.p01)
    (cubeFace_spatial _ (by decide))
  have hp' : HasQuaternionBlockDegree ((baseLinks 2).idxOf link)
      (if link ∈ edgesOf ((0,0,0,0),.p01) then 1 else 0) firstFaceTrace := by
    unfold firstFaceTrace
    exact hp
  have hs := product_degree link hm fs
    (fun face hf => cubeFace_spatial face (selected_mem hfs face hf))
  unfold selectedVacuumInsertion vacuumSelectionDegree
  exact hp'.mul hs

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

theorem selectedVacuumInsertion_supported (fs : List Z4Plaq) :
    SupportedQuaternionBlocks N (selectedVacuumInsertion fs) := by
  have hp : SupportedQuaternionBlocks N firstFaceTrace := by
    unfold firstFaceTrace
    exact face_supported ((0,0,0,0),.p01)
  unfold selectedVacuumInsertion
  exact supported_polyMul hp (product_supported fs)

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

/-- All sixty-two other literal original subsets vanish, without polynomial expansion. -/
theorem badSelection_haar_zero (fs : List Z4Plaq)
    (hfs : fs ∈ selections cubeFaces)
    (hsingle : fs ≠ singletonSelection)
    (hcomplement : fs ≠ complementSelection) :
    quaternionHaar N (selectedVacuumInsertion fs) ≈ 0 := by
  have he := badVacuumSelection_oddEdge fs hfs hsingle hcomplement
  exact haar_zero_of_odd_degree
    (List.idxOf_lt_length_of_mem (cubeLinks_in_carrier _ he.1)) _
    (selectedVacuumInsertion_supported fs)
    (selectedVacuumInsertion_degree fs hfs _ he.1) he.2

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumParity

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumParity.singletonSelection
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumParity.complementSelection
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumParity.selectedVacuumInsertion
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumParity.vacuumSelectionDegree
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumParity.vacuumOddEdge
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumParity.cubeVacuumSelections_parity_checked
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumParity.badVacuumSelection_oddEdge
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumParity.selectedVacuumInsertion_degree
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumParity.selectedVacuumInsertion_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumParity.badSelection_haar_zero
