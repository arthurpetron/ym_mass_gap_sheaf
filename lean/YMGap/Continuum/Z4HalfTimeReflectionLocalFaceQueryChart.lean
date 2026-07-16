/-
# Fixed local face queries in the adjacent half-time chart

A centered stage uses the odd box of side `2r+1`, whereas the half-time slab
uses the adjacent even ambient box of side `2r+2`.  This file re-encodes the
same fixed local polymers directly in that adjacent ambient box.  The root
list keeps exactly the original finite cardinality, lies inside the corrected
slab, and every connected slab residue has a carrier floor growing with the
receding stage.
-/

import YMGap.Continuum.Z4CanonicalPolymerFaceQueryDecoder
import YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierTail
import YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStabilityGeneral
import YMGap.Continuum.Z4SignedCenteredRecedingDiagonal

namespace YMGap.Continuum.Z4HalfTimeReflectionLocalFaceQueryChart

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryPairDichotomy
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierAnimal
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierFixedSize
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedPathCarrier
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStabilityGeneral
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStability
open YMGap.Continuum.Z4HalfTimeReflectionTopBoundaryTail
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding
open YMGap.Continuum.Z4SignedCenteredRecedingDiagonal
open YMGap.Continuum.Z4UniformShiftPhysicalTransport
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open Dir4

/-! ## 1. Direct adjacent-box re-encoding -/

theorem centralAmbient_eq_centeredBoxBase_add_one (radius : Nat) :
    centralAmbient radius = centeredBoxBase radius + 1 := by
  unfold centralAmbient centralExtent centeredBoxBase
  omega

/-- Re-encode the same geometrically centered root directly in the adjacent
even half-time ambient box. -/
def centralFaceQueryCanonicalRoot
    (radius base : Nat) (root : List Nat) : List Nat :=
  geometricSupportIds (centralAmbient radius)
    ((geometricPolymer base root).map (uniformShiftPlaquette radius))

theorem centralFaceQueryCanonicalRoot_sameSupport
    {radius base : Nat} (hbase : base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (centralAmbient radius)
        (centralFaceQueryCanonicalRoot radius base root))
      ((geometricPolymer base root).map
        (uniformShiftPlaquette radius)) := by
  unfold centralFaceQueryCanonicalRoot
  apply geometricSupportIds_sameSupport
  intro plaquette hplaquette
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
  apply boxPlaquettes_mono
    (show centeredBoxBase radius ≤ centralAmbient radius by
      rw [centralAmbient_eq_centeredBoxBase_add_one]
      omega)
  exact uniformShiftPlaquette_mem_centeredBase_of_le hbase
    (geometricPolymer_subset_box
      (canonicalSurfacePolymer_mem_faceSupports hroot) source hsource)

def centralFaceQueryCanonicalRoot_nonempty
    {radius base : Nat} (hbase : base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    Σ' face : Nat,
      face ∈ centralFaceQueryCanonicalRoot radius base root := by
  obtain ⟨sourceFace, hsourceFace⟩ :=
    canonicalSurfacePolymers_allNonempty base root hroot
  have hsource : boxPlaquetteAt base sourceFace ∈
      geometricPolymer base root :=
    List.mem_map.mpr ⟨sourceFace, hsourceFace, rfl⟩
  have hshifted :
      uniformShiftPlaquette radius (boxPlaquetteAt base sourceFace) ∈
        (geometricPolymer base root).map
          (uniformShiftPlaquette radius) :=
    List.mem_map.mpr ⟨_, hsource, rfl⟩
  have hencoded :=
    (centralFaceQueryCanonicalRoot_sameSupport hbase hroot).2 _ hshifted
  obtain ⟨targetFace, htargetFace, _⟩ :=
    decodeMapMember (boxPlaquetteAt (centralAmbient radius))
      (centralFaceQueryCanonicalRoot radius base root)
      (uniformShiftPlaquette radius (boxPlaquetteAt base sourceFace))
      hencoded
  exact ⟨targetFace, htargetFace⟩

def centralFaceQueryCanonicalRoot_connected
    {radius base : Nat} (hbase : base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    InternallyConnected (faceLinkAdjacentB (centralAmbient radius))
      (centralFaceQueryCanonicalRoot radius base root) := by
  unfold centralFaceQueryCanonicalRoot
  apply geometricSupportIds_connected
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    apply boxPlaquettes_mono
      (show centeredBoxBase radius ≤ centralAmbient radius by
        rw [centralAmbient_eq_centeredBoxBase_add_one]
        omega)
    exact uniformShiftPlaquette_mem_centeredBase_of_le hbase
      (geometricPolymer_subset_box
        (canonicalSurfacePolymer_mem_faceSupports hroot) source hsource)
  · exact uniformShiftConnected radius
      (numericalConnectedToGeometric
        ((canonicalSurfacePolymers_allConnected base) root hroot))

theorem centralFaceQueryCanonicalRoot_canonical
    {radius base : Nat} (hbase : base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centralFaceQueryCanonicalRoot radius base root ∈
      canonicalSurfacePolymers (centralAmbient radius) :=
  connectedFaceSupport_mem_canonicalSurfacePolymers
    (geometricSupportIds_mem_cutoffOneFaceSupports
      (centralAmbient radius)
      ((geometricPolymer base root).map
        (uniformShiftPlaquette radius)))
    (centralFaceQueryCanonicalRoot_nonempty hbase hroot)
    (centralFaceQueryCanonicalRoot_connected hbase hroot)

/-! ## 2. Exact adjacent odd/even root identity -/

theorem centralFaceQueryCanonicalRoot_eq_transport_centered
    {radius base : Nat} (hbase : base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centralFaceQueryCanonicalRoot radius base root =
      transportPolymer (centeredBoxBase radius) (centralAmbient radius)
        (centeredOffsetCanonicalRoot radius base root) := by
  have hcentered := centeredOffsetCanonicalRoot_canonical hbase hroot
  have hle : centeredBoxBase radius ≤ centralAmbient radius := by
    rw [centralAmbient_eq_centeredBoxBase_add_one]
    omega
  have htransport :=
    transportPolymer_mem_canonicalSurfacePolymers hle hcentered
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport
    (centralFaceQueryCanonicalRoot_canonical hbase hroot) htransport
  have hdirect := centralFaceQueryCanonicalRoot_sameSupport hbase hroot
  have hcenteredSupport :=
    centeredOffsetCanonicalRoot_sameSupport hbase hroot
  have htransportSupport := transportPolymer_sameSupport hle
    (canonicalSurfacePolymer_mem_faceSupports hcentered)
  exact sameSupport_trans hdirect
    (sameSupport_trans (sameSupport_symm hcenteredSupport)
      htransportSupport)

def centralFaceQueryCylinderRoots
    (radius base : Nat) (roots : List (List Nat)) : List (List Nat) :=
  roots.map (centralFaceQueryCanonicalRoot radius base)

@[simp] theorem centralFaceQueryCylinderRoots_length
    (radius base : Nat) (roots : List (List Nat)) :
    (centralFaceQueryCylinderRoots radius base roots).length =
      roots.length := by
  simp [centralFaceQueryCylinderRoots]

theorem centralFaceQueryCylinderRoots_canonical
    {radius base : Nat} (hbase : base ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target, target ∈ centralFaceQueryCylinderRoots radius base roots →
      target ∈ canonicalSurfacePolymers (centralAmbient radius) := by
  intro target htarget
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp htarget
  exact centralFaceQueryCanonicalRoot_canonical hbase
    (hroots source hsource)

theorem centralFaceQueryCylinderRoots_eq_transported_centered
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    centralFaceQueryCylinderRoots (base + stage) base roots =
      transportedCylinderRoots
        (centeredRecedingStageBase base stage)
        (centralAmbient (base + stage))
        (centeredRecedingStageRoots base stage roots) := by
  unfold centralFaceQueryCylinderRoots transportedCylinderRoots
    centeredRecedingStageRoots centeredRecedingStageRadius
    centeredRecedingStageBase centeredOffsetCylinderRoots
  rw [List.map_map]
  apply List.map_congr_left
  intro root hroot
  simp only [Function.comp_apply]
  exact centralFaceQueryCanonicalRoot_eq_transport_centered
    (Nat.le_add_right base stage) (hroots root hroot)

/-! ## 3. Slab support and a stage-growing time floor -/

theorem boxPlaquettes_centeredBoxBase_subset_centralSlab
    {radius : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boxPlaquettes (centeredBoxBase radius)) :
    plaquette ∈ boundaryCompleteSlabPlaquettes
      (centralExtent radius) := by
  apply (mem_boundaryCompleteSlabPlaquettes _ _).2
  constructor
  · apply boxPlaquettes_mono
      (show centeredBoxBase radius ≤ centralAmbient radius by
        rw [centralAmbient_eq_centeredBoxBase_add_one]
        omega)
    exact hplaquette
  · have hextent : centeredBoxBase radius = centralExtent radius := by
      unfold centeredBoxBase centralExtent
      omega
    rw [hextent] at hplaquette
    have hcoordinates := (mem_boxPlaquettes plaquette
      (centralExtent radius)).1 hplaquette
    obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
    change a < centralExtent radius ∧
      b < centralExtent radius ∧
      c < centralExtent radius ∧
      d < centralExtent radius at hcoordinates
    cases plane <;>
      simp [plaquetteTimeAdmissible] <;>
      omega

theorem centralFaceQueryCanonicalRoot_supported
    {radius base : Nat} (hbase : base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    canonicalPolymerSlabSupportedB (centralExtent radius)
      (centralFaceQueryCanonicalRoot radius base root) = true := by
  unfold canonicalPolymerSlabSupportedB
  apply List.all_eq_true.mpr
  intro face hface
  apply decide_eq_true
  have hgeom : boxPlaquetteAt (centralAmbient radius) face ∈
      geometricPolymer (centralAmbient radius)
        (centralFaceQueryCanonicalRoot radius base root) :=
    List.mem_map.mpr ⟨face, hface, rfl⟩
  have hshift :=
    (centralFaceQueryCanonicalRoot_sameSupport hbase hroot).1 _ hgeom
  obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hshift
  change boxPlaquetteAt (centralAmbient radius) face ∈
    boundaryCompleteSlabPlaquettes (centralExtent radius)
  rw [← hsourceEq]
  exact boxPlaquettes_centeredBoxBase_subset_centralSlab
    (uniformShiftPlaquette_mem_centeredBase_of_le hbase
      (geometricPolymer_subset_box
        (canonicalSurfacePolymer_mem_faceSupports hroot) source hsource))

theorem centralFaceQueryCanonicalRoot_time_lt
    {radius base : Nat} (hbase : base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ centralFaceQueryCanonicalRoot radius base root) :
    (boxPlaquetteAt (centralAmbient radius) face).1.2.2.2 <
      radius + base := by
  have hgeom : boxPlaquetteAt (centralAmbient radius) face ∈
      geometricPolymer (centralAmbient radius)
        (centralFaceQueryCanonicalRoot radius base root) :=
    List.mem_map.mpr ⟨face, hface, rfl⟩
  have hshift :=
    (centralFaceQueryCanonicalRoot_sameSupport hbase hroot).1 _ hgeom
  obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hshift
  have hbox := geometricPolymer_subset_box
    (canonicalSurfacePolymer_mem_faceSupports hroot) source hsource
  have hcoordinates := (mem_boxPlaquettes source base).1 hbox
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := source
  have hd : d < base := hcoordinates.2.2.2
  rw [← hsourceEq]
  simp only [uniformShiftPlaquette, uniformShiftVertex]
  omega

private theorem timeCoordinate_linf_floor_local
    {root q : Z4Plaq} {rootTime qTime distance : Nat}
    (hrootTime : root.1.2.2.2 = rootTime)
    (hqTime : q.1.2.2.2 = qTime)
    (hseparation : rootTime + distance ≤ qTime) :
    distance ≤ linfDist root q := by
  have hmetric := le_linfDist_comp root q x3
  obtain ⟨⟨a, b, c, d⟩, rootPlane⟩ := root
  obtain ⟨⟨e, f, g, h⟩, qPlane⟩ := q
  change d = rootTime at hrootTime
  change h = qTime at hqTime
  simp only [natDist, cPlaq, vComp] at hmetric
  omega

theorem centralFaceQueryCanonicalRoot_nonSlab_linf_floor
    {base stage : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈
      centralFaceQueryCanonicalRoot (base + stage) base root)
    {q : Z4Plaq}
    (hqBox : q ∈ boxPlaquettes (centralAmbient (base + stage)))
    (hqNot : q ∉
      boundaryCompleteSlabPlaquettes (centralExtent (base + stage))) :
    stage + 2 ≤
      linfDist
        (boxPlaquetteAt (centralAmbient (base + stage)) face) q := by
  have hrootTime := centralFaceQueryCanonicalRoot_time_lt
    (Nat.le_add_right base stage) hroot hface
  have hqTime := ambient_nonSlab_time_eq_extent hqBox hqNot
  apply timeCoordinate_linf_floor_local
    (rootTime :=
      (boxPlaquetteAt (centralAmbient (base + stage)) face).1.2.2.2)
    (qTime := centralExtent (base + stage))
  · rfl
  · exact hqTime
  · unfold centralExtent
    omega

/-! ## 4. Constant root count and the concrete connected-carrier floor -/

def centralFaceQueryCanonicalAtoms
    (radius base : Nat) (roots : List (List Nat))
    (hbase : base ≤ radius)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    List (CanonicalAtom (centralAmbient radius)) :=
  familyCanonicalAtoms (centralAmbient radius)
    (centralFaceQueryCylinderRoots radius base roots)
    (centralFaceQueryCylinderRoots_canonical hbase hroots)

theorem centralFaceQueryCanonicalAtoms_values
    (radius base : Nat) (roots : List (List Nat))
    (hbase : base ≤ radius)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    (centralFaceQueryCanonicalAtoms radius base roots hbase hroots).map
        Subtype.val =
      centralFaceQueryCylinderRoots radius base roots := by
  unfold centralFaceQueryCanonicalAtoms
  exact familyCanonicalAtoms_values (centralAmbient radius)
    (centralFaceQueryCylinderRoots radius base roots) _

@[simp] theorem centralFaceQueryCanonicalAtoms_length
    (radius base : Nat) (roots : List (List Nat))
    (hbase : base ≤ radius)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    (centralFaceQueryCanonicalAtoms radius base roots hbase hroots).length =
      roots.length := by
  have hvalues := congrArg List.length
    (centralFaceQueryCanonicalAtoms_values
      radius base roots hbase hroots)
  simpa only [List.length_map,
    centralFaceQueryCylinderRoots_length] using hvalues

theorem centralFaceQueryCanonicalAtoms_supported
    (radius base : Nat) (roots : List (List Nat))
    (hbase : base ≤ radius)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ atom, atom ∈
        centralFaceQueryCanonicalAtoms radius base roots hbase hroots →
      canonicalPolymerSlabSupportedB (centralExtent radius)
        atom.val = true := by
  intro atom hatom
  have hvalue : atom.val ∈
      (centralFaceQueryCanonicalAtoms radius base roots hbase hroots).map
        Subtype.val :=
    List.mem_map.mpr ⟨atom, hatom, rfl⟩
  rw [centralFaceQueryCanonicalAtoms_values] at hvalue
  obtain ⟨root, hroot, hvalueEq⟩ := List.mem_map.mp hvalue
  rw [← hvalueEq]
  exact centralFaceQueryCanonicalRoot_supported hbase
    (hroots root hroot)

theorem centralFaceQueryConnectedCarrierSupport_floor
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (centralAmbient (base + stage)))
    (entry : SlabConnectedSourceEntry (centralExtent (base + stage))
      (centralFaceQueryCanonicalAtoms (base + stage) base roots
        (Nat.le_add_right base stage) hroots) predicate) :
    stage + 3 ≤
      (slabConnectedCarrierSupport defaultRoot entry).length := by
  let atoms := centralFaceQueryCanonicalAtoms (base + stage) base roots
    (Nat.le_add_right base stage) hroots
  let selected := slabSourceRootAtom defaultRoot entry.val
  have hselected : selected ∈ atoms :=
    (slabSourceRootAtom_spec defaultRoot entry.val entry.property).2
  have hselectedValue : selected.val ∈
      centralFaceQueryCylinderRoots (base + stage) base roots := by
    have hmapped : selected.val ∈ atoms.map Subtype.val :=
      List.mem_map.mpr ⟨selected, hselected, rfl⟩
    simpa only [atoms,
      centralFaceQueryCanonicalAtoms_values] using hmapped
  obtain ⟨source, hsource, hsourceEq⟩ :=
    List.mem_map.mp hselectedValue
  have hrootFace := slabCanonicalAtomFirstFace_mem selected
  apply slabConnectedCarrierSupport_linf_size_floor
    defaultRoot
    (centralFaceQueryCanonicalAtoms_supported
      (base + stage) base roots (Nat.le_add_right base stage) hroots)
    entry hrootFace
  intro q hqBox hqOutside
  have hface : slabCanonicalAtomFirstFace selected ∈
      centralFaceQueryCanonicalRoot (base + stage) base source := by
    rw [hsourceEq]
    exact hrootFace
  exact centralFaceQueryCanonicalRoot_nonSlab_linf_floor
    (hroots source hsource) hface hqBox hqOutside

/-! ## 5. The derived conditional-law modulus for the fixed root chart -/

theorem couplingPhysicalCentralFaceQuery_givenSlab_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool)
    (defaultRoot : CanonicalAtom (centralAmbient (base + stage))) :
    let atoms := centralFaceQueryCanonicalAtoms
      (base + stage) base roots (Nat.le_add_right base stage) hroots
    Q'.abs
        (couplingKFamilyEventProbability coupling hcoupling cutoff
            (centralAmbient (base + stage))
            (slabMarkedCylinderEvent atoms predicate) -
          couplingParametricKPhysicalGivenSlabProbability
            coupling hcoupling cutoff (centralExtent (base + stage))
            (slabMarkedCylinderEvent atoms predicate)) ≤
      couplingSlabConditionalBoundaryEpsilon roots.length (stage + 3) := by
  dsimp only
  let atoms := centralFaceQueryCanonicalAtoms
    (base + stage) base roots (Nat.le_add_right base stage) hroots
  have hsupported : ∀ atom, atom ∈ atoms →
      canonicalPolymerSlabSupportedB (centralExtent (base + stage))
        atom.val = true := by
    simpa only [atoms] using
      (centralFaceQueryCanonicalAtoms_supported
        (base + stage) base roots (Nat.le_add_right base stage) hroots)
  have hfloorPredicate :
      ∀ entry : SlabConnectedSourceEntry
          (centralExtent (base + stage)) atoms predicate,
        stage + 3 ≤
          (slabConnectedCarrierSupport defaultRoot entry).length := by
    intro entry
    simpa only [atoms] using
      (centralFaceQueryConnectedCarrierSupport_floor
        hroots defaultRoot entry)
  have hfloorComplement :
      ∀ entry : SlabConnectedSourceEntry
          (centralExtent (base + stage)) atoms
            (complementSlabPredicate predicate),
        stage + 3 ≤
          (slabConnectedCarrierSupport defaultRoot entry).length := by
    intro entry
    simpa only [atoms] using
      (centralFaceQueryConnectedCarrierSupport_floor
        hroots defaultRoot entry)
  have hbound :=
    couplingPhysicalAmbient_givenSlabProbability_abs_sub_le_of_floors
      (extent := centralExtent (base + stage)) (roots := atoms)
      hcoupling hle cutoff predicate defaultRoot hsupported (stage + 3)
      hfloorPredicate hfloorComplement
  have hlength : atoms.length = roots.length := by
    simpa only [atoms] using
      (centralFaceQueryCanonicalAtoms_length
        (base + stage) base roots (Nat.le_add_right base stage) hroots)
  have hboundRoots := hlength ▸ hbound
  simpa only [atoms, centralAmbient] using hboundRoots

#print axioms centralFaceQueryCanonicalRoot_canonical
#print axioms centralFaceQueryCanonicalRoot_eq_transport_centered
#print axioms centralFaceQueryCylinderRoots_eq_transported_centered
#print axioms centralFaceQueryCanonicalRoot_supported
#print axioms centralFaceQueryCanonicalRoot_nonSlab_linf_floor
#print axioms centralFaceQueryCanonicalAtoms_length
#print axioms centralFaceQueryCanonicalAtoms_supported
#print axioms centralFaceQueryConnectedCarrierSupport_floor
#print axioms couplingPhysicalCentralFaceQuery_givenSlab_abs_sub_le

end YMGap.Continuum.Z4HalfTimeReflectionLocalFaceQueryChart
