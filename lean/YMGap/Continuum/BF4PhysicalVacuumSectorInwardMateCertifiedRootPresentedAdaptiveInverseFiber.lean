/-
# Injectivity of the certified presented adaptive code over one lowered target

The connected shape and physical words reconstruct the complete physical
strand-copy drop.  The complete auxiliary row word reconstructs the paired
drop table.  Consequently, once the lowered presented target and the root are
fixed, equality of the three-word adaptive codes reconstructs equality of the
literal source physical field and raw auxiliary assignment.

This is the injectivity kernel.  Packaging arbitrary finite fixed-target
families and counting them against the common carrier is downstream.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveEntropyCode
import YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryDecoder
import YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDropCode

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveInverseFiber

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveEntropyCode
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPhysicalMultiplicityCode
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryDecoder
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalDropDecoder
open YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAdaptiveAuxiliaryProduction
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Reconstruction congruence for dependent presented targets -/

/-- Raw presented-assignment reconstruction depends only on the auxiliary
word table and on the lowered presented target.  `HEq` records equality of the
targets before their physical indices have been identified. -/
theorem reconstructPresentedAssignmentRaw_eq_of_auxiliaryWords_eq
    (left right : SlabFaceStrandComponentDropCode)
    {K extent : Nat}
    {leftTargetPhysical rightTargetPhysical : SlabLabelling}
    (links : List SlabLink)
    (leftTarget : PresentedSlabFusionWitnessAssignment
      K extent leftTargetPhysical links)
    (rightTarget : PresentedSlabFusionWitnessAssignment
      K extent rightTargetPhysical links)
    (hphysical : leftTargetPhysical = rightTargetPhysical)
    (htarget : HEq leftTarget rightTarget)
    (hauxiliary : left.auxiliaryWords = right.auxiliaryWords) :
    reconstructPresentedAssignmentRaw left links leftTarget =
      reconstructPresentedAssignmentRaw right links rightTarget := by
  cases hphysical
  have htargetEq : leftTarget = rightTarget := eq_of_heq htarget
  subst rightTarget
  unfold reconstructPresentedAssignmentRaw reconstructPresentedAuxiliaryAt
    decodePresentedAuxiliaryDrop
  rw [hauxiliary]

/-- The paired auxiliary table is determined by its fixed-order value row. -/
theorem slabAuxiliaryDropWordsFrom_eq_of_map_eq
    (left right : SlabLink -> List Nat) (links : List SlabLink)
    (hrows : links.map left = links.map right) :
    slabAuxiliaryDropWordsFrom links left =
      slabAuxiliaryDropWordsFrom links right := by
  unfold slabAuxiliaryDropWordsFrom
  exact pairedMap_eq_of_map_eq left right links hrows

/-! ## 2. Flat inverse data and its generic injectivity theorem -/

/-- Pair a fixed displayed-link list with an already-produced row list. -/
def auxiliaryWordsOfRows :
    List SlabLink -> List (List Nat) -> List (SlabLink × List Nat)
  | [], _ => []
  | _, [] => []
  | link :: links, row :: rows =>
      (link, row) :: auxiliaryWordsOfRows links rows

/-- Pairing a mapped row reconstructs the original keyed table exactly. -/
theorem auxiliaryWordsOfRows_map (wordAt : SlabLink -> List Nat) :
    forall links : List SlabLink,
    auxiliaryWordsOfRows links (links.map wordAt) =
      slabAuxiliaryDropWordsFrom links wordAt
  | [] => rfl
  | link :: links => by
      simp only [List.map_cons, auxiliaryWordsOfRows,
        slabAuxiliaryDropWordsFrom]
      rw [auxiliaryWordsOfRows_map wordAt links]
      rfl

/-- Turn a complete fixed-order row word back into the drop-code interface
consumed by presented assignment reconstruction.  Physical faces are
irrelevant for this reconstruction. -/
def adaptiveRowsDropCode (extent : Nat) (rows : List (List Nat)) :
    SlabFaceStrandComponentDropCode where
  physicalFaces := []
  auxiliaryWords :=
    auxiliaryWordsOfRows (boundaryCompleteSlabLinks extent) rows

/-- For any supported presented selection, its adaptive row word reconstructs
the complete raw source assignment from the lowered presented target. -/
theorem presentedSelectionAdaptiveAuxiliaryRows_reconstructRaw
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : PresentedSlabFusionWitnessAssignment K extent physical
      (boundaryCompleteSlabLinks extent)}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection K extent
      physical (boundaryCompleteSlabLinks extent) assignment) :
    reconstructPresentedAssignmentRaw
        (adaptiveRowsDropCode extent
          (presentedSelectionAdaptiveAuxiliaryRows selection))
        (boundaryCompleteSlabLinks extent)
        selection.closed.loweredAssignment =
      presentedSlabFusionWitnessAssignmentRaw
        (boundaryCompleteSlabLinks extent) assignment := by
  rw [← presentedSlabSupportedSelectionDropCode_reconstructPresentedAssignmentRaw
    selection]
  apply reconstructPresentedAssignmentRaw_eq_of_auxiliaryWords_eq
    (adaptiveRowsDropCode extent
      (presentedSelectionAdaptiveAuxiliaryRows selection))
    (presentedSlabSupportedSelectionDropCode selection)
    (boundaryCompleteSlabLinks extent)
    selection.closed.loweredAssignment selection.closed.loweredAssignment
    (Eq.refl selection.closed.lowerPhysical) (HEq.refl _) 
  unfold adaptiveRowsDropCode presentedSelectionAdaptiveAuxiliaryRows
    presentedSlabSupportedSelectionDropCode
  exact auxiliaryWordsOfRows_map
    (presentedSlabSupportedSelectionAuxiliaryDropWordAt selection)
    (boundaryCompleteSlabLinks extent)

/-- The complete, flat interface consumed by adaptive inverse decoding.  The
large strand construction is compiled into this record once; downstream
injectivity never unfolds it. -/
structure PresentedAdaptiveInverseData (K extent : Nat) : Type where
  rootFaceId : Nat
  shapeCode : List (Fin (z4Chain.D + 1))
  physicalMultiplicityCode : List Nat
  auxiliaryRows : List (List Nat)
  sourcePhysical : SlabLabelling
  lowerPhysical : SlabLabelling
  lowerAssignment : PresentedSlabFusionWitnessAssignment K extent
    lowerPhysical (boundaryCompleteSlabLinks extent)
  sourceRaw : SlabFusionWitnessAssignment
  physicalDrop : Nat -> Nat
  peelCount : Nat -> Nat
  physicalDrop_decode : forall faceId,
    componentPhysicalDropDecode extent rootFaceId shapeCode
      physicalMultiplicityCode faceId = physicalDrop faceId
  peelCount_eq_physicalDrop : forall faceId,
    peelCount faceId = physicalDrop faceId
  reconstructPhysical :
    raiseEdgeLabellingBy lowerPhysical peelCount = sourcePhysical
  reconstructRaw :
    reconstructPresentedAssignmentRaw
      (adaptiveRowsDropCode extent auxiliaryRows)
      (boundaryCompleteSlabLinks extent) lowerAssignment = sourceRaw

/-- The three finite words carried by flat inverse data. -/
def PresentedAdaptiveInverseData.code
    {K extent : Nat} (data : PresentedAdaptiveInverseData K extent) :
    ComponentAdaptiveEntropyCode :=
  componentAdaptiveEntropyCodeOfWords data.shapeCode
    data.physicalMultiplicityCode data.auxiliaryRows

/-- Equality of flat adaptive codes over one root and one lowered dependent
target reconstructs equality of both source fields. -/
theorem PresentedAdaptiveInverseData.sourceData_eq_of_code_eq
    {K extent : Nat}
    (left right : PresentedAdaptiveInverseData K extent)
    (hroot : left.rootFaceId = right.rootFaceId)
    (hlowerPhysical : left.lowerPhysical = right.lowerPhysical)
    (hlowerAssignment : HEq left.lowerAssignment right.lowerAssignment)
    (hcode : left.code = right.code) :
    left.sourcePhysical = right.sourcePhysical ∧
      left.sourceRaw = right.sourceRaw := by
  have hshape := congrArg ComponentAdaptiveEntropyCode.shape hcode
  have hphysical :=
    congrArg ComponentAdaptiveEntropyCode.physicalMultiplicity hcode
  have hrows := congrArg ComponentAdaptiveEntropyCode.auxiliaryRows hcode
  unfold PresentedAdaptiveInverseData.code at hshape hphysical hrows
  rw [componentAdaptiveEntropyCodeOfWords_shape,
    componentAdaptiveEntropyCodeOfWords_shape] at hshape
  rw [componentAdaptiveEntropyCodeOfWords_physicalMultiplicity,
    componentAdaptiveEntropyCodeOfWords_physicalMultiplicity] at hphysical
  rw [componentAdaptiveEntropyCodeOfWords_auxiliaryRows,
    componentAdaptiveEntropyCodeOfWords_auxiliaryRows] at hrows
  have hdrop : forall faceId,
      left.physicalDrop faceId = right.physicalDrop faceId := by
    intro faceId
    rw [← left.physicalDrop_decode faceId,
      ← right.physicalDrop_decode faceId,
      hroot, hshape, hphysical]
  have hpeelCount : left.peelCount = right.peelCount := by
    funext faceId
    rw [left.peelCount_eq_physicalDrop faceId,
      right.peelCount_eq_physicalDrop faceId]
    exact hdrop faceId
  have hauxiliary :
      (adaptiveRowsDropCode extent left.auxiliaryRows).auxiliaryWords =
        (adaptiveRowsDropCode extent right.auxiliaryRows).auxiliaryWords := by
    rw [hrows]
  constructor
  · calc
      left.sourcePhysical =
          raiseEdgeLabellingBy left.lowerPhysical left.peelCount :=
        left.reconstructPhysical.symm
      _ = raiseEdgeLabellingBy right.lowerPhysical right.peelCount := by
        rw [hlowerPhysical, hpeelCount]
      _ = right.sourcePhysical := right.reconstructPhysical
  · calc
      left.sourceRaw = reconstructPresentedAssignmentRaw
          (adaptiveRowsDropCode extent left.auxiliaryRows)
          (boundaryCompleteSlabLinks extent) left.lowerAssignment :=
        left.reconstructRaw.symm
      _ = reconstructPresentedAssignmentRaw
          (adaptiveRowsDropCode extent right.auxiliaryRows)
          (boundaryCompleteSlabLinks extent) right.lowerAssignment :=
        reconstructPresentedAssignmentRaw_eq_of_auxiliaryWords_eq
          (adaptiveRowsDropCode extent left.auxiliaryRows)
          (adaptiveRowsDropCode extent right.auxiliaryRows)
          (boundaryCompleteSlabLinks extent)
          left.lowerAssignment right.lowerAssignment hlowerPhysical
          hlowerAssignment hauxiliary
      _ = right.sourceRaw := right.reconstructRaw

/-! ## 3. Compile the certified BF4 source into the flat interface -/

/-- The actual certified two-root source, compiled once into the flat inverse
interface used by the generic injectivity theorem. -/
def certifiedStretchedComponentUnionAdaptiveInverseData
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    PresentedAdaptiveInverseData K 1 where
  rootFaceId := (certifiedStretchedComponentUnionShapePhysicalData
    stretched background).rootFaceId
  shapeCode := certifiedStretchedComponentUnionConnectedShapeCode
    stretched background
  physicalMultiplicityCode :=
    certifiedStretchedComponentUnionPhysicalMultiplicityBinaryCode
      stretched background
  auxiliaryRows := certifiedStretchedComponentUnionAdaptiveAuxiliaryRows
    stretched background
  sourcePhysical := physical
  lowerPhysical := CertifiedStretchedComponentUnionLowerPhysical
    stretched background
  lowerAssignment := certifiedStretchedComponentUnionLoweredAssignment
    stretched background
  sourceRaw := presentedSlabFusionWitnessAssignmentRaw
    (boundaryCompleteSlabLinks 1)
    (completePresentedSlabSourceOfCertifiedCube
      K physical hK hbounded stretched.certified background)
  physicalDrop := slabFaceStrandSelectionCount
    (certifiedStretchedComponentUnionSupportedSelection
      stretched background).closed.selected
  peelCount := fun faceId =>
    (certifiedStretchedComponentUnionSupportedSelection
      stretched background).peelFaces.count faceId
  physicalDrop_decode :=
    certifiedStretchedComponentUnionPhysicalDropDecode stretched background
  peelCount_eq_physicalDrop :=
    (certifiedStretchedComponentUnionSupportedSelection
      stretched background).peelFaces_count
  reconstructPhysical :=
    certifiedStretchedComponentUnion_reconstructPhysical stretched background
  reconstructRaw :=
    presentedSelectionAdaptiveAuxiliaryRows_reconstructRaw
      (certifiedStretchedComponentUnionSupportedSelection stretched background)

#print axioms reconstructPresentedAssignmentRaw_eq_of_auxiliaryWords_eq
#print axioms slabAuxiliaryDropWordsFrom_eq_of_map_eq
#print axioms auxiliaryWordsOfRows
#print axioms auxiliaryWordsOfRows_map
#print axioms adaptiveRowsDropCode
#print axioms presentedSelectionAdaptiveAuxiliaryRows_reconstructRaw
#print axioms PresentedAdaptiveInverseData
#print axioms PresentedAdaptiveInverseData.code
#print axioms PresentedAdaptiveInverseData.sourceData_eq_of_code_eq
#print axioms certifiedStretchedComponentUnionAdaptiveInverseData

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveInverseFiber
