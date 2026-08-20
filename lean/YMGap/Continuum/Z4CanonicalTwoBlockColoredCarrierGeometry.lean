/-
# Geometry and weight of the two-block colored carrier

The two color supports stored by the recoverable carrier have the same union
as the complete loop-erased disagreement path.  For the strict doubled-time
blocks this union therefore inherits the temporal size floor.  The exact
strong-coupling envelope then pays one factor per union face, leaving only the
two compatible background activities.
-/

import YMGap.Continuum.Z4CanonicalTwoBlockColoredPathCarrier

namespace YMGap.Continuum.Z4CanonicalTwoBlockColoredCarrierGeometry

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
open YMGap.Continuum.Z4CanonicalConnectedCarrierWeight
open YMGap.Continuum.Z4CanonicalConnectedPathCarrier
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockColoredPathCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedResidueCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockSwitchSummation
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeCarrierFloor
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedEventRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

abbrev StrictDoubledTimeConnectedEntry
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (firstPredicate secondPredicate : List Bool → Bool) :=
  TwoBlockConnectedEntry
    (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
    (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
    firstPredicate secondPredicate

theorem strictDoubledTimeConnectedFirst_value_mem
    {radius base shift : Nat}
    {hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius}
    {roots : List (List Nat)}
    {hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : StrictDoubledTimeConnectedEntry hadmissible hroots
      firstPredicate secondPredicate) :
    (twoBlockConnectedFirst entry).val ∈
      roots.map (strictJointDoubledTimeMixedLowerRoot
        radius base shift) := by
  change (twoBlockConnectedFirst entry).val ∈
    strictJointDoubledTimeLowerRootValues radius base shift roots
  rw [← strictJointDoubledTimeLowerRootAtoms_values
    hadmissible hroots]
  exact List.mem_map.mpr
    ⟨twoBlockConnectedFirst entry,
      twoBlockConnectedFirst_mem entry, rfl⟩

theorem strictDoubledTimeConnectedSecond_value_mem
    {radius base shift : Nat}
    {hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius}
    {roots : List (List Nat)}
    {hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : StrictDoubledTimeConnectedEntry hadmissible hroots
      firstPredicate secondPredicate) :
    (twoBlockConnectedSecond entry).val ∈
      roots.map (strictJointDoubledTimeMixedUpperRoot
        radius base shift) := by
  change (twoBlockConnectedSecond entry).val ∈
    strictJointDoubledTimeUpperRootValues radius base shift roots
  rw [← strictJointDoubledTimeUpperRootAtoms_values
    hadmissible hroots]
  exact List.mem_map.mpr
    ⟨twoBlockConnectedSecond entry,
      twoBlockConnectedSecond_mem entry, rfl⟩

theorem strictDoubledTimeConnectedEndpoints_ne
    {radius base shift : Nat}
    {hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius}
    {roots : List (List Nat)}
    {hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : StrictDoubledTimeConnectedEntry hadmissible hroots
      firstPredicate secondPredicate) :
    twoBlockConnectedFirst entry ≠ twoBlockConnectedSecond entry := by
  obtain ⟨lowerRoot, hlowerRoot, hfirstEq⟩ :=
    decodeMapMember
      (strictJointDoubledTimeMixedLowerRoot radius base shift)
      roots (twoBlockConnectedFirst entry).val
      (strictDoubledTimeConnectedFirst_value_mem entry)
  obtain ⟨upperRoot, hupperRoot, hsecondEq⟩ :=
    decodeMapMember
      (strictJointDoubledTimeMixedUpperRoot radius base shift)
      roots (twoBlockConnectedSecond entry).val
      (strictDoubledTimeConnectedSecond_value_mem entry)
  let firstFace := canonicalSurfacePolymers_allNonempty
    (centralAmbient radius) (twoBlockConnectedFirst entry).val
    (twoBlockConnectedFirst entry).property
  intro heq
  have heqValue : (twoBlockConnectedFirst entry).val =
      (twoBlockConnectedSecond entry).val := congrArg Subtype.val heq
  have hfirstFace : firstFace.1 ∈
      strictJointDoubledTimeMixedLowerRoot
        radius base shift lowerRoot := by
    rw [hfirstEq]
    exact firstFace.2
  have hsecondFace : firstFace.1 ∈
      strictJointDoubledTimeMixedUpperRoot
        radius base shift upperRoot := by
    rw [hsecondEq, ← heqValue]
    exact firstFace.2
  have hfloor := strictJointDoubledTimeMixedRoots_linf_floor
    hadmissible (hroots lowerRoot hlowerRoot)
    (hroots upperRoot hupperRoot) hfirstFace hsecondFace
  simp [linfDist, natDist] at hfloor

def twoBlockConnectedColoredSupport
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) : List Nat :=
  familyUnionSupport n
    (twoBlockConnectedPathLeftFamily entry ++
      twoBlockConnectedPathRightFamily entry)

def twoBlockConnectedFullPathSupport
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) : List Nat :=
  familyUnionSupport n (twoBlockConnectedPathValues entry)

theorem twoBlockConnectedPathAtom_mem_coloredFamily
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate)
    (hne : twoBlockConnectedFirst entry ≠
      twoBlockConnectedSecond entry)
    {atom : CanonicalAtom n}
    (hatom : atom ∈ twoBlockConnectedPathAtoms entry) :
    atom.val ∈ twoBlockConnectedPathLeftFamily entry ∨
      atom.val ∈ twoBlockConnectedPathRightFamily entry := by
  have htest : twoBlockConnectedPathTest entry atom.val = true := by
    unfold twoBlockConnectedPathTest twoBlockConnectedPathValues
    apply (memberB_eq_true_iff _ _).2
    exact List.mem_map.mpr ⟨atom, hatom, rfl⟩
  rcases twoBlockConnectedPathAtoms_exclusive entry hne atom hatom with
      hleft | hright
  · apply Or.inl
    unfold twoBlockConnectedPathLeftFamily
    apply List.mem_filter.mpr
    exact ⟨(canonicalFamilyAtom_mem_iff
      (twoBlockSourceLeftCompatible entry.val) atom).1
        ((memberB_eq_true_iff _ _).1 hleft.1), htest⟩
  · apply Or.inr
    unfold twoBlockConnectedPathRightFamily
    apply List.mem_filter.mpr
    exact ⟨(canonicalFamilyAtom_mem_iff
      (twoBlockSourceRightCompatible entry.val) atom).1
        ((memberB_eq_true_iff _ _).1 hright.2), htest⟩

theorem twoBlockConnectedColoredSupport_eq_fullPathSupport
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate)
    (hne : twoBlockConnectedFirst entry ≠
      twoBlockConnectedSecond entry) :
    twoBlockConnectedColoredSupport entry =
      twoBlockConnectedFullPathSupport entry := by
  apply sublists_eq_of_mem_iff (physicalFaceEdges n)
    (twoBlockConnectedColoredSupport entry)
    (twoBlockConnectedFullPathSupport entry)
    (physicalFaceEdges_nodup n)
    (familyUnionSupport_mem_cutoffOneFaceSupports n _)
    (familyUnionSupport_mem_cutoffOneFaceSupports n _)
  intro face
  constructor
  · intro hface
    obtain ⟨hphysical, polymer, hpolymer, hpolymerFace⟩ :=
      (mem_familyUnionSupport_iff n _ face).1 hface
    have htest : twoBlockConnectedPathTest entry polymer = true := by
      rcases List.mem_append.mp hpolymer with hleft | hright
      · exact (List.mem_filter.mp hleft).2
      · exact (List.mem_filter.mp hright).2
    exact (mem_familyUnionSupport_iff n _ face).2
      ⟨hphysical, polymer,
        (memberB_eq_true_iff _ _).1 htest, hpolymerFace⟩
  · intro hface
    obtain ⟨hphysical, polymer, hpolymer, hpolymerFace⟩ :=
      (mem_familyUnionSupport_iff n _ face).1 hface
    obtain ⟨atom, hatom, hatomValue⟩ :=
      decodeMapMember Subtype.val (twoBlockConnectedPathAtoms entry)
        polymer hpolymer
    have hcolored := twoBlockConnectedPathAtom_mem_coloredFamily
      entry hne (atom := atom) (by
        simpa [twoBlockConnectedPathValues] using hatom)
    exact (mem_familyUnionSupport_iff n _ face).2
      ⟨hphysical, polymer, (by
        rw [← hatomValue]
        exact List.mem_append.mpr hcolored), hpolymerFace⟩

theorem twoBlockConnectedFullPathSupport_eq_carrierSupport
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :
    twoBlockConnectedFullPathSupport entry =
      twoBlockConnectedCarrierSupport
        (twoBlockSourceLeftCompatible entry.val)
        (twoBlockSourceRightCompatible entry.val)
        (twoBlockConnectedFirst entry)
        (twoBlockConnectedSecond entry)
        (twoBlockConnectedEndpoints_reach entry) := by
  unfold twoBlockConnectedFullPathSupport
    Z4CanonicalTwoBlockColoredPathCarrier.twoBlockConnectedPathValues
    Z4CanonicalTwoBlockColoredPathCarrier.twoBlockConnectedPathAtoms
    Z4CanonicalTwoBlockColoredPathCarrier.twoBlockConnectedSourcePath
    twoBlockConnectedCarrierSupport
    Z4CanonicalTwoBlockConnectedCarrier.twoBlockConnectedPathAtoms
  rfl

theorem strictDoubledTimeConnectedColoredSupport_size_floor
    {radius base shift : Nat}
    {hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius}
    {roots : List (List Nat)}
    {hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : StrictDoubledTimeConnectedEntry hadmissible hroots
      firstPredicate secondPredicate) :
    shift + shift + 6 ≤
      (twoBlockConnectedColoredSupport entry).length := by
  rw [twoBlockConnectedColoredSupport_eq_fullPathSupport entry
    (strictDoubledTimeConnectedEndpoints_ne entry)]
  rw [twoBlockConnectedFullPathSupport_eq_carrierSupport entry]
  exact (strictJointDoubledTimeConnectedBranch_size_floor
    hadmissible hroots
    (twoBlockSourceLeftCompatible entry.val)
    (twoBlockSourceRightCompatible entry.val)
    (twoBlockConnectedFirst entry)
    (twoBlockConnectedSecond entry)
    (strictDoubledTimeConnectedFirst_value_mem entry)
    (strictDoubledTimeConnectedSecond_value_mem entry)
    (twoBlockConnectedEndpoints_reach entry)).2.2.2

theorem twoBlockConnectedColoredSupport_length_le_pathFaceCount
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :
    (twoBlockConnectedColoredSupport entry).length ≤
      familyFaceCount (twoBlockConnectedPathLeftFamily entry) +
        familyFaceCount (twoBlockConnectedPathRightFamily entry) := by
  have hbound := familyUnionSupport_length_le_familyFaceCount n
    (twoBlockConnectedPathLeftFamily entry ++
      twoBlockConnectedPathRightFamily entry)
  rw [familyFaceCount_append] at hbound
  simpa [twoBlockConnectedColoredSupport] using hbound

theorem twoBlockConnectedPathPairWeight_le_supportPow
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :
    twoBlockConnectedPathPairWeight anchorCoupling entry ≤
      anchorPerFaceEnvelope ^
        (twoBlockConnectedColoredSupport entry).length := by
  have hleft := compatibleFamily_activity_le_totalFacePow
    (twoBlockConnectedPathLeftFamily_mem entry)
  have hright := compatibleFamily_activity_le_totalFacePow
    (twoBlockConnectedPathRightFamily_mem entry)
  have hright0 := canonicalSurfaceFamilyActivity_nonnegative n
    (twoBlockConnectedPathRightFamily entry)
  have hleftPow0 : (0 : Q') ≤ anchorPerFaceEnvelope ^
      familyFaceCount (twoBlockConnectedPathLeftFamily entry) :=
    Q'.pow_nonneg anchorPerFaceEnvelope (by decide) _
  have hpair := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hleft hright0)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hright hleftPow0)
      (Q'.le_of_eqv (Q'.eqv_symm
        (Q'.pow_add_eqv anchorPerFaceEnvelope
          (familyFaceCount (twoBlockConnectedPathLeftFamily entry))
          (familyFaceCount (twoBlockConnectedPathRightFamily entry))))))
  exact Q'.le_trans' _ _ _ hpair
    (pow_base_antitone (r := anchorPerFaceEnvelope)
      (by decide) (by decide)
      (twoBlockConnectedColoredSupport_length_le_pathFaceCount entry))

theorem twoBlockConnectedSourcePairWeight_le_support_background
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :
    twoBlockSourcePairWeight anchorCoupling entry.val ≤
      anchorPerFaceEnvelope ^
          (twoBlockConnectedColoredSupport entry).length *
        twoBlockConnectedBackgroundPairWeight anchorCoupling entry := by
  have hbackground0 : (0 : Q') ≤
      twoBlockConnectedBackgroundPairWeight anchorCoupling entry := by
    unfold twoBlockConnectedBackgroundPairWeight
    exact Q'.mul_nonneg _ _
      (canonicalSurfaceFamilyActivity_nonnegative n _)
      (canonicalSurfaceFamilyActivity_nonnegative n _)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (twoBlockConnectedSourcePairWeight_factor anchorCoupling entry))
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (twoBlockConnectedPathPairWeight_le_supportPow entry)
      hbackground0)

#print axioms strictDoubledTimeConnectedEndpoints_ne
#print axioms twoBlockConnectedColoredSupport_eq_fullPathSupport
#print axioms strictDoubledTimeConnectedColoredSupport_size_floor
#print axioms twoBlockConnectedSourcePairWeight_le_support_background

end YMGap.Continuum.Z4CanonicalTwoBlockColoredCarrierGeometry
