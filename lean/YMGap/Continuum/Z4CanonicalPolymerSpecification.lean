/-
# Interior characterization of the cross-volume polymer specification

The transport module embeds every smaller-box compatible family in a larger
box.  Here we prove the converse on the geometric interior: a canonical
larger-box polymer whose whole plaquette support lies in the smaller box is
exactly the transport of a canonical smaller-box polymer.  This identifies
the genuinely new configurations as boundary-reaching configurations and is
the finite combinatorial input required before an Ursell cancellation proof.
-/

import YMGap.Continuum.Z4CanonicalPolymerTransport

namespace YMGap.Continuum.Z4CanonicalPolymerSpecification

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4PhysicalSurfaceComponents

/-! ## 1. Restriction of an interior polymer -/

/-- A target polymer is geometrically inside box `n` when every decoded
plaquette in its support occurs in `boxPlaquettes n`. -/
def PolymerInsideBox (n m : Nat) (support : List Nat) : Prop :=
  ∀ plaquette, plaquette ∈ geometricPolymer m support →
    plaquette ∈ boxPlaquettes n

/-- Re-encode a target polymer in the numerical coordinates of a smaller
box. -/
def restrictPolymer (n m : Nat) (support : List Nat) : List Nat :=
  geometricSupportIds n (geometricPolymer m support)

theorem restrictPolymer_sameSupport
    {n m : Nat} {support : List Nat}
    (hinside : PolymerInsideBox n m support) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer n (restrictPolymer n m support))
      (geometricPolymer m support) := by
  unfold restrictPolymer
  exact geometricSupportIds_sameSupport hinside

def restrictPolymer_nonempty
    {n m : Nat} {support : List Nat}
    (hpolymer : support ∈ canonicalSurfacePolymers m)
    (hinside : PolymerInsideBox n m support) :
    Σ' face : Nat, face ∈ restrictPolymer n m support := by
  obtain ⟨targetFace, htargetFace⟩ :=
    canonicalSurfacePolymers_allNonempty m support hpolymer
  have htargetGeom : boxPlaquetteAt m targetFace ∈
      geometricPolymer m support :=
    List.mem_map.mpr ⟨targetFace, htargetFace, rfl⟩
  have hsourceGeom :=
    (restrictPolymer_sameSupport hinside).2
      (boxPlaquetteAt m targetFace) htargetGeom
  obtain ⟨sourceFace, hsourceFace, _⟩ :=
    decodeMapMember (boxPlaquetteAt n)
      (restrictPolymer n m support)
      (boxPlaquetteAt m targetFace) hsourceGeom
  exact ⟨sourceFace, hsourceFace⟩

def restrictPolymer_connected
    {n m : Nat} {support : List Nat}
    (hpolymer : support ∈ canonicalSurfacePolymers m)
    (hinside : PolymerInsideBox n m support) :
    InternallyConnected (faceLinkAdjacentB n)
      (restrictPolymer n m support) := by
  unfold restrictPolymer
  exact geometricSupportIds_connected hinside
    (numericalConnectedToGeometric
      (canonicalSurfacePolymers_allConnected m support hpolymer))

/-- Every target canonical polymer contained in the smaller geometry has a
canonical smaller-box restriction. -/
theorem restrictPolymer_mem_canonicalSurfacePolymers
    {n m : Nat} {support : List Nat}
    (hpolymer : support ∈ canonicalSurfacePolymers m)
    (hinside : PolymerInsideBox n m support) :
    restrictPolymer n m support ∈ canonicalSurfacePolymers n :=
  connectedFaceSupport_mem_canonicalSurfacePolymers
    (geometricSupportIds_mem_cutoffOneFaceSupports n
      (geometricPolymer m support))
    (restrictPolymer_nonempty hpolymer hinside)
    (restrictPolymer_connected hpolymer hinside)

/-- Restriction followed by transport is literally the original canonical
target polymer. -/
theorem transport_restrictPolymer_eq
    {n m : Nat} (hnm : n ≤ m) {support : List Nat}
    (hpolymer : support ∈ canonicalSurfacePolymers m)
    (hinside : PolymerInsideBox n m support) :
    transportPolymer n m (restrictPolymer n m support) = support := by
  have hrestricted :=
    restrictPolymer_mem_canonicalSurfacePolymers hpolymer hinside
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport
    (transportPolymer_mem_canonicalSurfacePolymers hnm hrestricted)
    hpolymer
  have htransport := transportPolymer_sameSupport hnm
    (canonicalSurfacePolymer_mem_faceSupports hrestricted)
  exact sameSupport_trans (sameSupport_symm htransport)
    (restrictPolymer_sameSupport hinside)

/-! ## 2. Restriction of a whole compatible family -/

def FamilyInsideBox (n m : Nat) (family : List (List Nat)) : Prop :=
  ∀ support, support ∈ family → PolymerInsideBox n m support

/-- Every literal member of the transported ensemble is geometrically
contained in the source box.  Together with
`family_mem_embeddedCompatibleFamilies_of_inside` below, this gives the exact
inside/embedded specification needed by component switching. -/
theorem familyInsideBox_of_mem_embeddedCompatibleFamilies
    {n m : Nat} (hnm : n ≤ m) {family : List (List Nat)}
    (hfamily : family ∈ embeddedCompatibleFamilies n m) :
    FamilyInsideBox n m family := by
  obtain ⟨sourceFamily, hsourceFamily, hfamilyEq⟩ :=
    List.mem_map.mp hfamily
  rw [← hfamilyEq]
  intro target htarget
  obtain ⟨source, hsource, rfl⟩ :=
    (mem_embeddedTransportFamily_iff hnm hsourceFamily target).1 htarget
  intro plaquette hplaquette
  have hsourcePlaquette :=
    (transportPolymer_sameSupport hnm
      (canonicalSurfacePolymer_mem_faceSupports
        (compatibleAmbientFamily_member_ambient
          hsourceFamily hsource))).2 plaquette hplaquette
  exact geometricPolymer_subset_box
    (canonicalSurfacePolymer_mem_faceSupports
      (compatibleAmbientFamily_member_ambient hsourceFamily hsource))
    plaquette hsourcePlaquette

def restrictedSourceFamily (n m : Nat)
    (family : List (List Nat)) : List (List Nat) :=
  ambientOrderedFamily n (family.map (restrictPolymer n m))

theorem mem_restrictedSourceFamily_iff
    {n m : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies m)
    (hinside : FamilyInsideBox n m family)
    (source : List Nat) :
    source ∈ restrictedSourceFamily n m family ↔
      ∃ target, target ∈ family ∧
        source = restrictPolymer n m target := by
  unfold restrictedSourceFamily
  rw [mem_ambientOrderedFamily_iff]
  constructor
  · intro hsource
    obtain ⟨target, htarget, heq⟩ := List.mem_map.mp hsource.2
    exact ⟨target, htarget, heq.symm⟩
  · rintro ⟨target, htarget, rfl⟩
    constructor
    · exact restrictPolymer_mem_canonicalSurfacePolymers
        (compatibleAmbientFamily_member_ambient hfamily htarget)
        (hinside target htarget)
    · exact List.mem_map.mpr ⟨target, htarget, rfl⟩

theorem restrictedSourceFamily_invariants
    {n m : Nat} (hnm : n ≤ m) {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies m)
    (hinside : FamilyInsideBox n m family) :
    DistinctDisjoint (restrictedSourceFamily n m family) ∧
      DistinctSeparated (faceLinkAdjacentB n)
        (restrictedSourceFamily n m family) := by
  have htargetFacts := compatibleAmbientFamily_invariants hfamily
  constructor
  · intro sourceLeft hsourceLeft sourceRight hsourceRight hsourceNe
    obtain ⟨targetLeft, htargetLeft, hleftEq⟩ :=
      (mem_restrictedSourceFamily_iff hfamily hinside sourceLeft).1
        hsourceLeft
    obtain ⟨targetRight, htargetRight, hrightEq⟩ :=
      (mem_restrictedSourceFamily_iff hfamily hinside sourceRight).1
        hsourceRight
    have htargetNe : targetLeft ≠ targetRight := by
      intro heq
      subst targetRight
      exact hsourceNe (hleftEq.trans hrightEq.symm)
    have htargetDisjoint := htargetFacts.1
      targetLeft htargetLeft targetRight htargetRight htargetNe
    have hleftTransport := transport_restrictPolymer_eq hnm
      (compatibleAmbientFamily_member_ambient hfamily htargetLeft)
      (hinside targetLeft htargetLeft)
    have hrightTransport := transport_restrictPolymer_eq hnm
      (compatibleAmbientFamily_member_ambient hfamily htargetRight)
      (hinside targetRight htargetRight)
    rw [← hleftTransport, ← hrightTransport] at htargetDisjoint
    rw [hleftEq, hrightEq]
    exact supportsDisjoint_of_transport hnm
      (canonicalSurfacePolymer_mem_faceSupports
        (restrictPolymer_mem_canonicalSurfacePolymers
          (compatibleAmbientFamily_member_ambient hfamily htargetLeft)
          (hinside targetLeft htargetLeft)))
      (canonicalSurfacePolymer_mem_faceSupports
        (restrictPolymer_mem_canonicalSurfacePolymers
          (compatibleAmbientFamily_member_ambient hfamily htargetRight)
          (hinside targetRight htargetRight)))
      htargetDisjoint
  · intro sourceLeft hsourceLeft sourceRight hsourceRight hsourceNe
    obtain ⟨targetLeft, htargetLeft, hleftEq⟩ :=
      (mem_restrictedSourceFamily_iff hfamily hinside sourceLeft).1
        hsourceLeft
    obtain ⟨targetRight, htargetRight, hrightEq⟩ :=
      (mem_restrictedSourceFamily_iff hfamily hinside sourceRight).1
        hsourceRight
    have htargetNe : targetLeft ≠ targetRight := by
      intro heq
      subst targetRight
      exact hsourceNe (hleftEq.trans hrightEq.symm)
    have htargetSeparated := htargetFacts.2
      targetLeft htargetLeft targetRight htargetRight htargetNe
    have hleftTransport := transport_restrictPolymer_eq hnm
      (compatibleAmbientFamily_member_ambient hfamily htargetLeft)
      (hinside targetLeft htargetLeft)
    have hrightTransport := transport_restrictPolymer_eq hnm
      (compatibleAmbientFamily_member_ambient hfamily htargetRight)
      (hinside targetRight htargetRight)
    rw [← hleftTransport, ← hrightTransport] at htargetSeparated
    rw [hleftEq, hrightEq]
    exact supportsSeparated_of_transport hnm
      (canonicalSurfacePolymer_mem_faceSupports
        (restrictPolymer_mem_canonicalSurfacePolymers
          (compatibleAmbientFamily_member_ambient hfamily htargetLeft)
          (hinside targetLeft htargetLeft)))
      (canonicalSurfacePolymer_mem_faceSupports
        (restrictPolymer_mem_canonicalSurfacePolymers
          (compatibleAmbientFamily_member_ambient hfamily htargetRight)
          (hinside targetRight htargetRight)))
      htargetSeparated

theorem restrictedSourceFamily_mem_compatible
    {n m : Nat} (hnm : n ≤ m) {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies m)
    (hinside : FamilyInsideBox n m family) :
    restrictedSourceFamily n m family ∈
      canonicalCompatibleAmbientFamilies n := by
  unfold canonicalCompatibleAmbientFamilies
  apply List.mem_filter.mpr
  refine ⟨?_, ?_⟩
  · unfold restrictedSourceFamily ambientOrderedFamily
    exact filter_mem_sublists _ _
  · exact canonicalFamilyCompatibleB_true n
      (restrictedSourceFamily n m family)
      (ambientOrderedFamily_nodup n
        (family.map (restrictPolymer n m)))
      (restrictedSourceFamily_invariants hnm hfamily hinside).1
      (restrictedSourceFamily_invariants hnm hfamily hinside).2

/-- A compatible target family wholly contained in the smaller geometry is
literally the embedded image of its canonical restricted source family. -/
theorem embedded_restrictedSourceFamily_eq
    {n m : Nat} (hnm : n ≤ m) {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies m)
    (hinside : FamilyInsideBox n m family) :
    embeddedTransportFamily n m (restrictedSourceFamily n m family) =
      family := by
  have hsourceFamily :=
    restrictedSourceFamily_mem_compatible hnm hfamily hinside
  apply sublists_eq_of_mem_iff (canonicalSurfacePolymers m)
    (embeddedTransportFamily n m (restrictedSourceFamily n m family))
    family (canonicalSurfacePolymers_nodup m)
  · unfold embeddedTransportFamily ambientOrderedFamily
    exact filter_mem_sublists _ _
  · exact compatibleAmbientFamily_sublist hfamily
  · intro polymer
    constructor
    · intro hpolymer
      obtain ⟨source, hsource, hpolymerEq⟩ :=
        (mem_embeddedTransportFamily_iff hnm hsourceFamily polymer).1
          hpolymer
      obtain ⟨target, htarget, hsourceEq⟩ :=
        (mem_restrictedSourceFamily_iff hfamily hinside source).1
          hsource
      have htransport := transport_restrictPolymer_eq hnm
        (compatibleAmbientFamily_member_ambient hfamily htarget)
        (hinside target htarget)
      rw [hpolymerEq, hsourceEq, htransport]
      exact htarget
    · intro hpolymer
      have hsource : restrictPolymer n m polymer ∈
          restrictedSourceFamily n m family :=
        (mem_restrictedSourceFamily_iff hfamily hinside
          (restrictPolymer n m polymer)).2
          ⟨polymer, hpolymer, rfl⟩
      have hembedded :
          transportPolymer n m (restrictPolymer n m polymer) ∈
            embeddedTransportFamily n m
              (restrictedSourceFamily n m family) :=
        (mem_embeddedTransportFamily_iff hnm hsourceFamily
          (transportPolymer n m (restrictPolymer n m polymer))).2
          ⟨restrictPolymer n m polymer, hsource, rfl⟩
      rw [transport_restrictPolymer_eq hnm
        (compatibleAmbientFamily_member_ambient hfamily hpolymer)
        (hinside polymer hpolymer)] at hembedded
      exact hembedded

/-- Equivalently, every compatible target family supported inside the smaller
box occurs in the exact embedded subensemble. -/
theorem family_mem_embeddedCompatibleFamilies_of_inside
    {n m : Nat} (hnm : n ≤ m) {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies m)
    (hinside : FamilyInsideBox n m family) :
    family ∈ embeddedCompatibleFamilies n m := by
  unfold embeddedCompatibleFamilies
  exact List.mem_map.mpr
    ⟨restrictedSourceFamily n m family,
      restrictedSourceFamily_mem_compatible hnm hfamily hinside,
      embedded_restrictedSourceFamily_eq hnm hfamily hinside⟩

/-! ## 3. A decidable boundary witness for the complement -/

def polymerInsideBoxB (n m : Nat) (support : List Nat) : Bool :=
  (geometricPolymer m support).all
    (fun plaquette => decide (plaquette ∈ boxPlaquettes n))

def familyInsideBoxB (n m : Nat) (family : List (List Nat)) : Bool :=
  family.all (polymerInsideBoxB n m)

theorem polymerInsideBoxB_true_iff
    (n m : Nat) (support : List Nat) :
    polymerInsideBoxB n m support = true ↔
      PolymerInsideBox n m support := by
  constructor
  · intro h plaquette hplaquette
    unfold polymerInsideBoxB at h
    have htest := List.all_eq_true.mp h plaquette hplaquette
    simpa only [decide_eq_true_eq] using htest
  · intro h
    unfold polymerInsideBoxB
    apply List.all_eq_true.mpr
    intro plaquette hplaquette
    simpa only [decide_eq_true_eq] using h plaquette hplaquette

theorem familyInsideBoxB_true_iff
    (n m : Nat) (family : List (List Nat)) :
    familyInsideBoxB n m family = true ↔
      FamilyInsideBox n m family := by
  constructor
  · intro h support hsupport
    unfold familyInsideBoxB at h
    exact (polymerInsideBoxB_true_iff n m support).1
      (List.all_eq_true.mp h support hsupport)
  · intro h
    unfold familyInsideBoxB
    apply List.all_eq_true.mpr
    intro support hsupport
    exact (polymerInsideBoxB_true_iff n m support).2
      (h support hsupport)

private theorem exists_false_of_all_false {A : Type} (test : A → Bool) :
    ∀ xs : List A, xs.all test = false →
      ∃ item, item ∈ xs ∧ test item = false
  | [], h => by cases h
  | head :: tail, h => by
      cases hhead : test head with
      | false => exact ⟨head, List.mem_cons_self, hhead⟩
      | true =>
          have htail : tail.all test = false := by
            simp only [List.all_cons, hhead, Bool.true_and] at h
            exact h
          obtain ⟨item, hitem, hfalse⟩ :=
            exists_false_of_all_false test tail htail
          exact ⟨item, List.mem_cons_of_mem head hitem, hfalse⟩

theorem polymerInsideBoxB_false_witness
    {n m : Nat} {support : List Nat}
    (hfalse : polymerInsideBoxB n m support = false) :
    ∃ plaquette, plaquette ∈ geometricPolymer m support ∧
      plaquette ∉ boxPlaquettes n := by
  unfold polymerInsideBoxB at hfalse
  obtain ⟨plaquette, hplaquette, htest⟩ :=
    exists_false_of_all_false
      (fun item => decide (item ∈ boxPlaquettes n))
      (geometricPolymer m support) hfalse
  refine ⟨plaquette, hplaquette, ?_⟩
  intro hinside
  have htrue : decide (plaquette ∈ boxPlaquettes n) = true := by
    simpa only [decide_eq_true_eq] using hinside
  rw [htest] at htrue
  exact Bool.false_ne_true htrue

theorem familyInsideBoxB_false_witness
    {n m : Nat} {family : List (List Nat)}
    (hfalse : familyInsideBoxB n m family = false) :
    ∃ support, support ∈ family ∧
      ∃ plaquette, plaquette ∈ geometricPolymer m support ∧
        plaquette ∉ boxPlaquettes n := by
  unfold familyInsideBoxB at hfalse
  obtain ⟨support, hsupport, hsupportFalse⟩ :=
    exists_false_of_all_false (polymerInsideBoxB n m) family hfalse
  obtain ⟨plaquette, hplaquette, houtside⟩ :=
    polymerInsideBoxB_false_witness hsupportFalse
  exact ⟨support, hsupport, plaquette, hplaquette, houtside⟩

/-- Every compatible target family outside the exact embedded subensemble has
a concrete canonical polymer and plaquette that leave the smaller box. -/
theorem family_not_mem_embedded_has_outside_witness
    {n m : Nat} (hnm : n ≤ m) {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies m)
    (hnot : family ∉ embeddedCompatibleFamilies n m) :
    ∃ support, support ∈ family ∧
      ∃ plaquette, plaquette ∈ geometricPolymer m support ∧
        plaquette ∉ boxPlaquettes n := by
  have hfalse : familyInsideBoxB n m family = false := by
    cases hinside : familyInsideBoxB n m family with
    | false => rfl
    | true =>
        have hmem := family_mem_embeddedCompatibleFamilies_of_inside
          hnm hfamily ((familyInsideBoxB_true_iff n m family).1 hinside)
        exact False.elim (hnot hmem)
  exact familyInsideBoxB_false_witness hfalse

end YMGap.Continuum.Z4CanonicalPolymerSpecification

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalPolymerSpecification.restrictPolymer_sameSupport
#print axioms YMGap.Continuum.Z4CanonicalPolymerSpecification.restrictPolymer_mem_canonicalSurfacePolymers
#print axioms YMGap.Continuum.Z4CanonicalPolymerSpecification.transport_restrictPolymer_eq
#print axioms YMGap.Continuum.Z4CanonicalPolymerSpecification.familyInsideBox_of_mem_embeddedCompatibleFamilies
#print axioms YMGap.Continuum.Z4CanonicalPolymerSpecification.restrictedSourceFamily_mem_compatible
#print axioms YMGap.Continuum.Z4CanonicalPolymerSpecification.family_mem_embeddedCompatibleFamilies_of_inside
#print axioms YMGap.Continuum.Z4CanonicalPolymerSpecification.family_not_mem_embedded_has_outside_witness
