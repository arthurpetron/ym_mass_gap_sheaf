/-
# The local support pair as one fixed-cardinality marked cylinder

The left and right local support decoders produce occurrence fingerprints of
the strict lower and strict upper roots.  Concatenating those two root lists
therefore presents every local Gram entry as one ordinary marked cylinder
with twice the original finite number of roots.
-/

import YMGap.Continuum.Z4HalfTimeReflectionLocalPairConditionalLaw
import YMGap.Continuum.Z4HalfTimeReflectionUpperSupportLocalQuery

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder

set_option maxRecDepth 100000
set_option maxHeartbeats 100000

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryPairDichotomy
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalFamilyFaceSupportDecoder
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLocalFaceQueryChart
open YMGap.Continuum.Z4HalfTimeReflectionLocalPairConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionLocalSupportPushforward
open YMGap.Continuum.Z4HalfTimeReflectionLowerSupportLocalQuery
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierAnimal
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierFixedSize
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedPathCarrier
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStability
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStabilityGeneral
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionTopBoundaryTail
open YMGap.Continuum.Z4HalfTimeReflectionUpperSupportLocalQuery
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open Dir4

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The concatenated strict chart and its split predicate -/

def centralStrictJointCylinderRoots
    (radius base : Nat) (roots : List (List Nat)) : List (List Nat) :=
  centralStrictLowerCylinderRoots radius base roots ++
    centralStrictUpperCylinderRoots radius base roots

@[simp] theorem centralStrictJointCylinderRoots_length
    (radius base : Nat) (roots : List (List Nat)) :
    (centralStrictJointCylinderRoots radius base roots).length =
      roots.length + roots.length := by
  simp [centralStrictJointCylinderRoots]

theorem centralStrictJointCylinderRoots_canonical
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target, target ∈ centralStrictJointCylinderRoots radius base roots →
      target ∈ canonicalSurfacePolymers (centralAmbient radius) := by
  intro target htarget
  have hparts := List.mem_append.mp htarget
  cases hparts with
  | inl hlower =>
      exact centralStrictLowerCylinderRoots_canonical
        hbase hroots target hlower
  | inr hupper =>
      exact centralStrictUpperCylinderRoots_canonical
        hbase hroots target hupper

/-- Split the concatenated occurrence fingerprint after the lower-root block.
Using `take` and `drop` keeps the event exact even for targets whose supplied
bit lists have an unexpected length. -/
def centralStrictJointPairPredicate
    (rootCount : Nat) (left right : List Bool) : List Bool → Bool :=
  fun bits => decide
    (bits.take rootCount = left ∧ bits.drop rootCount = right)

theorem familyOccurrenceFingerprint_append
    (first second : List (List Nat)) (family : List (List Nat)) :
    familyOccurrenceFingerprint (first ++ second) family =
      familyOccurrenceFingerprint first family ++
        familyOccurrenceFingerprint second family := by
  unfold familyOccurrenceFingerprint
  exact List.map_append

/-- Evaluating the joint cylinder is literally the conjunction of the two
individual fingerprint equalities. -/
theorem centralStrictJointPairCylinderEvent_eq
    (radius base : Nat) (roots : List (List Nat))
    (left right : List Bool) (family : List (List Nat)) :
    sourceCylinderEvent
        (centralStrictJointCylinderRoots radius base roots)
        (centralStrictJointPairPredicate roots.length left right)
        family =
      decide
        (familyOccurrenceFingerprint
              (centralStrictLowerCylinderRoots radius base roots) family =
            left ∧
          familyOccurrenceFingerprint
              (centralStrictUpperCylinderRoots radius base roots) family =
            right) := by
  unfold sourceCylinderEvent cylinderEvent
    centralStrictJointPairPredicate centralStrictJointCylinderRoots
  rw [familyOccurrenceFingerprint_append]
  have hlength :
      (familyOccurrenceFingerprint
        (centralStrictLowerCylinderRoots radius base roots) family).length =
        roots.length := by
    rw [familyOccurrenceFingerprint_length,
      centralStrictLowerCylinderRoots_length]
  rw [← hlength, List.take_append_length, List.drop_append_length]

/-! ## 2. Canonical atoms and exact fixed cardinality -/

def centralStrictJointCanonicalAtoms
    (radius base : Nat) (roots : List (List Nat))
    (hbase : strictQueryBase base ≤ radius)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    List (CanonicalAtom (centralAmbient radius)) :=
  familyCanonicalAtoms (centralAmbient radius)
    (centralStrictJointCylinderRoots radius base roots)
    (centralStrictJointCylinderRoots_canonical hbase hroots)

theorem centralStrictJointCanonicalAtoms_values
    (radius base : Nat) (roots : List (List Nat))
    (hbase : strictQueryBase base ≤ radius)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    (centralStrictJointCanonicalAtoms
      radius base roots hbase hroots).map Subtype.val =
        centralStrictJointCylinderRoots radius base roots := by
  unfold centralStrictJointCanonicalAtoms
  exact familyCanonicalAtoms_values (centralAmbient radius)
    (centralStrictJointCylinderRoots radius base roots) _

@[simp] theorem centralStrictJointCanonicalAtoms_length
    (radius base : Nat) (roots : List (List Nat))
    (hbase : strictQueryBase base ≤ radius)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    (centralStrictJointCanonicalAtoms
      radius base roots hbase hroots).length =
        roots.length + roots.length := by
  have hvalues := congrArg List.length
    (centralStrictJointCanonicalAtoms_values
      radius base roots hbase hroots)
  simpa only [List.length_map,
    centralStrictJointCylinderRoots_length] using hvalues

theorem centralStrictJointMarkedCylinderEvent_eq
    (radius base : Nat) (roots : List (List Nat))
    (hbase : strictQueryBase base ≤ radius)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    slabMarkedCylinderEvent
        (centralStrictJointCanonicalAtoms
          radius base roots hbase hroots)
        (centralStrictJointPairPredicate roots.length left right) =
      sourceCylinderEvent
        (centralStrictJointCylinderRoots radius base roots)
        (centralStrictJointPairPredicate roots.length left right) := by
  funext family
  unfold slabMarkedCylinderEvent sourceCylinderEvent
  exact congrArg
    (fun markedRoots => cylinderEvent markedRoots
      (centralStrictJointPairPredicate roots.length left right) family)
    (centralStrictJointCanonicalAtoms_values
      radius base roots hbase hroots)

/-! ## 3. Specializing the exact local conditional law -/

def centralStrictLocalQueryCode
    (radius base : Nat) (roots : List (List Nat)) :
    List Nat → List Bool :=
  centralLowerSupportQueryFingerprint radius
    (centralStrictLowerCylinderRoots radius base roots)

theorem centralLocalSupportPairFamilyEvent_strict_physical
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) (physical : EdgeLabelling) :
    centralLocalSupportPairFamilyEvent radius
        (centralStrictLocalQueryCode radius base roots)
        left right
        (physicalCanonicalAmbientFamily
          (centralAmbient radius) physical) =
      sourceCylinderEvent
        (centralStrictJointCylinderRoots radius base roots)
        (centralStrictJointPairPredicate roots.length left right)
        (physicalCanonicalAmbientFamily
          (centralAmbient radius) physical) := by
  rw [centralLocalSupportPairFamilyEvent_physical]
  unfold centralStrictLocalQueryCode
  rw [centralStrictLowerSupportQueryFingerprint_eq_familyOccurrence
      hbase hroots physical,
    centralStrictReflectedUpperSupportQueryFingerprint_eq_familyOccurrence
      hbase hroots physical,
    centralStrictJointPairCylinderEvent_eq]

theorem couplingPhysicalGivenSlab_strictLocal_eq_marked
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling) (cutoff : Nat)
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    couplingParametricKPhysicalGivenSlabProbability
        coupling hcoupling cutoff (centralExtent radius)
        (centralLocalSupportPairFamilyEvent radius
          (centralStrictLocalQueryCode radius base roots) left right) =
      couplingParametricKPhysicalGivenSlabProbability
        coupling hcoupling cutoff (centralExtent radius)
        (slabMarkedCylinderEvent
          (centralStrictJointCanonicalAtoms
            radius base roots hbase hroots)
          (centralStrictJointPairPredicate roots.length left right)) := by
  have hmarked := centralStrictJointMarkedCylinderEvent_eq
    radius base roots hbase hroots left right
  have hevents :
      (fun physical =>
        ambientSlabSupportedB (centralExtent radius) physical &&
          cutoffOneLiftedFamilyEvent (centralExtent radius + 1)
            (centralLocalSupportPairFamilyEvent radius
              (centralStrictLocalQueryCode radius base roots)
              left right) physical) =
      (fun physical =>
        ambientSlabSupportedB (centralExtent radius) physical &&
          cutoffOneLiftedFamilyEvent (centralExtent radius + 1)
            (slabMarkedCylinderEvent
              (centralStrictJointCanonicalAtoms
                radius base roots hbase hroots)
              (centralStrictJointPairPredicate roots.length left right))
            physical) := by
    funext physical
    unfold cutoffOneLiftedFamilyEvent
    rw [hmarked]
    exact congrArg
      (ambientSlabSupportedB (centralExtent radius) physical && ·)
      (centralLocalSupportPairFamilyEvent_strict_physical
        hbase hroots left right physical)
  unfold couplingParametricKPhysicalGivenSlabProbability
  rw [hevents]

/-- Every normalized local Gram entry is exactly the corrected-slab law of
one marked cylinder with `2 * roots.length` (written constructively as
`roots.length + roots.length`) canonical atoms. -/
theorem centralNormalizedLocalSupportPairLaw_eq_strictMarkedCylinder
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling) (cutoff : Nat)
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    centralNormalizedLocalSupportPairLaw
        coupling hcoupling cutoff radius
        (centralStrictLocalQueryCode radius base roots) left right ≈
      couplingParametricKPhysicalGivenSlabProbability
        coupling hcoupling cutoff (centralExtent radius)
        (slabMarkedCylinderEvent
          (centralStrictJointCanonicalAtoms
            radius base roots hbase hroots)
          (centralStrictJointPairPredicate roots.length left right)) := by
  refine Q'.eqv_trans _ _ _
    (centralNormalizedLocalSupportPairLaw_eq_physicalGivenSlab
      coupling hcoupling cutoff radius
      (centralStrictLocalQueryCode radius base roots) left right) ?_
  exact Q'.eqv_of_eq
    (couplingPhysicalGivenSlab_strictLocal_eq_marked
      coupling hcoupling cutoff hbase hroots left right)

/-! ## 4. The stage-growing conditional modulus for the joint chart -/

theorem centralStrictJointCanonicalAtoms_supported
    (radius base : Nat) (roots : List (List Nat))
    (hbase : strictQueryBase base ≤ radius)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ atom, atom ∈ centralStrictJointCanonicalAtoms
        radius base roots hbase hroots →
      canonicalPolymerSlabSupportedB (centralExtent radius)
        atom.val = true := by
  intro atom hatom
  have hvalue : atom.val ∈
      (centralStrictJointCanonicalAtoms
        radius base roots hbase hroots).map Subtype.val :=
    List.mem_map.mpr ⟨atom, hatom, rfl⟩
  rw [centralStrictJointCanonicalAtoms_values] at hvalue
  have hparts := List.mem_append.mp hvalue
  cases hparts with
  | inl hlower =>
      obtain ⟨source, hsource, hvalueEq⟩ := List.mem_map.mp hlower
      rw [← hvalueEq]
      exact centralReflectedCanonicalRoot_supported
        (centralStrictUpperCanonicalRoot_canonical hbase
          (hroots source hsource))
        (centralStrictUpperCanonicalRoot_supported hbase
          (hroots source hsource))
  | inr hupper =>
      obtain ⟨source, hsource, hvalueEq⟩ := List.mem_map.mp hupper
      rw [← hvalueEq]
      exact centralStrictUpperCanonicalRoot_supported hbase
        (hroots source hsource)

private theorem timeCoordinate_linf_floor_joint
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

theorem centralStrictJointRoot_nonSlab_linf_floor
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    {target : List Nat}
    (htarget : target ∈ centralStrictJointCylinderRoots
      (strictQueryBase base + stage) base roots)
    {face : Nat} (hface : face ∈ target)
    {q : Z4Plaq}
    (hqBox : q ∈ boxPlaquettes
      (centralAmbient (strictQueryBase base + stage)))
    (hqNot : q ∉ boundaryCompleteSlabPlaquettes
      (centralExtent (strictQueryBase base + stage))) :
    stage + 2 ≤ linfDist
      (boxPlaquetteAt
        (centralAmbient (strictQueryBase base + stage)) face) q := by
  have hparts := List.mem_append.mp htarget
  cases hparts with
  | inl hlower =>
      obtain ⟨source, hsource, htargetEq⟩ := List.mem_map.mp hlower
      rw [← htargetEq] at hface
      have htime := centralStrictLowerCanonicalRoot_time_add_two_le
        (Nat.le_add_right (strictQueryBase base) stage)
        (hroots source hsource) hface
      have hqTime := ambient_nonSlab_time_eq_extent hqBox hqNot
      apply timeCoordinate_linf_floor_joint
        (rootTime :=
          (boxPlaquetteAt
            (centralAmbient (strictQueryBase base + stage))
            face).1.2.2.2)
        (qTime := centralExtent (strictQueryBase base + stage))
      · rfl
      · exact hqTime
      · unfold centralExtent
        omega
  | inr hupper =>
      obtain ⟨source, hsource, htargetEq⟩ := List.mem_map.mp hupper
      rw [← htargetEq] at hface
      exact centralFaceQueryCanonicalRoot_nonSlab_linf_floor
        (base := strictQueryBase base) (stage := stage)
        (strictQuerySourceRoot_canonical (hroots source hsource))
        hface hqBox hqNot

theorem centralStrictJointConnectedCarrierSupport_floor
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom
      (centralAmbient (strictQueryBase base + stage)))
    (entry : SlabConnectedSourceEntry
      (centralExtent (strictQueryBase base + stage))
      (centralStrictJointCanonicalAtoms
        (strictQueryBase base + stage) base roots
        (Nat.le_add_right (strictQueryBase base) stage) hroots)
      predicate) :
    stage + 3 ≤
      (slabConnectedCarrierSupport defaultRoot entry).length := by
  let atoms := centralStrictJointCanonicalAtoms
    (strictQueryBase base + stage) base roots
    (Nat.le_add_right (strictQueryBase base) stage) hroots
  let selected := slabSourceRootAtom defaultRoot entry.val
  have hselected : selected ∈ atoms :=
    (slabSourceRootAtom_spec defaultRoot entry.val entry.property).2
  have hselectedValue : selected.val ∈
      centralStrictJointCylinderRoots
        (strictQueryBase base + stage) base roots := by
    have hmapped : selected.val ∈ atoms.map Subtype.val :=
      List.mem_map.mpr ⟨selected, hselected, rfl⟩
    simpa only [atoms,
      centralStrictJointCanonicalAtoms_values] using hmapped
  have hrootFace := slabCanonicalAtomFirstFace_mem selected
  apply slabConnectedCarrierSupport_linf_size_floor
    defaultRoot
    (centralStrictJointCanonicalAtoms_supported
      (strictQueryBase base + stage) base roots
      (Nat.le_add_right (strictQueryBase base) stage) hroots)
    entry hrootFace
  intro q hqBox hqOutside
  exact centralStrictJointRoot_nonSlab_linf_floor
    hroots hselectedValue hrootFace hqBox hqOutside

/-- The literal ambient-versus-corrected-slab discrepancy for the joint local
event has the same `stage + 3` carrier floor as a one-sided chart.  Its only
fixed cost is the doubled finite root count. -/
theorem couplingPhysicalStrictJoint_givenSlab_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool)
    (defaultRoot : CanonicalAtom
      (centralAmbient (strictQueryBase base + stage))) :
    let atoms := centralStrictJointCanonicalAtoms
      (strictQueryBase base + stage) base roots
      (Nat.le_add_right (strictQueryBase base) stage) hroots
    let predicate := centralStrictJointPairPredicate
      roots.length left right
    Q'.abs
        (couplingKFamilyEventProbability coupling hcoupling cutoff
            (centralAmbient (strictQueryBase base + stage))
            (slabMarkedCylinderEvent atoms predicate) -
          couplingParametricKPhysicalGivenSlabProbability
            coupling hcoupling cutoff
            (centralExtent (strictQueryBase base + stage))
            (slabMarkedCylinderEvent atoms predicate)) ≤
      couplingSlabConditionalBoundaryEpsilon
        (roots.length + roots.length) (stage + 3) := by
  dsimp only
  let atoms := centralStrictJointCanonicalAtoms
    (strictQueryBase base + stage) base roots
    (Nat.le_add_right (strictQueryBase base) stage) hroots
  let predicate := centralStrictJointPairPredicate roots.length left right
  have hsupported : ∀ atom, atom ∈ atoms →
      canonicalPolymerSlabSupportedB
        (centralExtent (strictQueryBase base + stage)) atom.val = true := by
    simpa only [atoms] using
      (centralStrictJointCanonicalAtoms_supported
        (strictQueryBase base + stage) base roots
        (Nat.le_add_right (strictQueryBase base) stage) hroots)
  have hfloorPredicate :
      ∀ entry : SlabConnectedSourceEntry
          (centralExtent (strictQueryBase base + stage)) atoms predicate,
        stage + 3 ≤
          (slabConnectedCarrierSupport defaultRoot entry).length := by
    intro entry
    simpa only [atoms, predicate] using
      (centralStrictJointConnectedCarrierSupport_floor
        hroots defaultRoot entry)
  have hfloorComplement :
      ∀ entry : SlabConnectedSourceEntry
          (centralExtent (strictQueryBase base + stage)) atoms
            (complementSlabPredicate predicate),
        stage + 3 ≤
          (slabConnectedCarrierSupport defaultRoot entry).length := by
    intro entry
    simpa only [atoms, predicate] using
      (centralStrictJointConnectedCarrierSupport_floor
        hroots defaultRoot entry)
  have hbound :=
    couplingPhysicalAmbient_givenSlabProbability_abs_sub_le_of_floors
      (extent := centralExtent (strictQueryBase base + stage))
      (roots := atoms) hcoupling hle cutoff predicate defaultRoot
      hsupported (stage + 3) hfloorPredicate hfloorComplement
  have hlength : atoms.length = roots.length + roots.length := by
    simpa only [atoms] using
      (centralStrictJointCanonicalAtoms_length
        (strictQueryBase base + stage) base roots
        (Nat.le_add_right (strictQueryBase base) stage) hroots)
  have hboundRoots := hlength ▸ hbound
  simpa only [atoms, predicate, centralAmbient] using hboundRoots

#print axioms centralStrictJointCylinderRoots_canonical
#print axioms familyOccurrenceFingerprint_append
#print axioms centralStrictJointPairCylinderEvent_eq
#print axioms centralStrictJointCanonicalAtoms_values
#print axioms centralStrictJointCanonicalAtoms_length
#print axioms centralStrictJointMarkedCylinderEvent_eq
#print axioms centralLocalSupportPairFamilyEvent_strict_physical
#print axioms couplingPhysicalGivenSlab_strictLocal_eq_marked
#print axioms centralNormalizedLocalSupportPairLaw_eq_strictMarkedCylinder
#print axioms centralStrictJointCanonicalAtoms_supported
#print axioms centralStrictJointRoot_nonSlab_linf_floor
#print axioms centralStrictJointConnectedCarrierSupport_floor
#print axioms couplingPhysicalStrictJoint_givenSlab_abs_sub_le

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
