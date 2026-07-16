/-
# Exact range of the corrected canonical polymer universe

Every corrected-compatible subfamily of the finite ambient polymer list is the
canonical component family of its union support.  Conversely every exact gas
family is corrected-compatible after ambient ordering.  This closes the finite
range theorem required to identify the actual cutoff-one spin foam with the
corrected finite polymer partition, rather than only inject it into one.
-/

import YMGap.Continuum.Z4CanonicalPolymerUniverse
import YMGap.Continuum.Z4PhysicalSurfaceComponentUniqueness

namespace YMGap.Continuum.Z4CanonicalPolymerRange

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphComponentUniqueness
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4PhysicalSurfaceComponentUniqueness
open YMGap.Continuum.Z4PhysicalSurfaceComponents

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The finite union support of a family -/

def familyContainsFaceB (face : Nat) : List (List Nat) → Bool
  | [] => false
  | polymer :: rest =>
      decide (face ∈ polymer) || familyContainsFaceB face rest

theorem familyContainsFaceB_true_iff (face : Nat) :
    ∀ family : List (List Nat), familyContainsFaceB face family = true ↔
      ∃ polymer, polymer ∈ family ∧ face ∈ polymer
  | [] => by simp [familyContainsFaceB]
  | polymer :: rest => by
      simp [familyContainsFaceB, familyContainsFaceB_true_iff face rest]

def familyUnionSupport (n : Nat) (family : List (List Nat)) : List Nat :=
  (physicalFaceEdges n).filter
    (fun face => familyContainsFaceB face family)

theorem mem_familyUnionSupport_iff
    (n : Nat) (family : List (List Nat)) (face : Nat) :
    face ∈ familyUnionSupport n family ↔
      face ∈ physicalFaceEdges n ∧
        ∃ polymer, polymer ∈ family ∧ face ∈ polymer := by
  unfold familyUnionSupport
  rw [List.mem_filter, familyContainsFaceB_true_iff]

theorem familyUnionSupport_mem_cutoffOneFaceSupports
    (n : Nat) (family : List (List Nat)) :
    familyUnionSupport n family ∈ cutoffOneFaceSupports n := by
  unfold familyUnionSupport cutoffOneFaceSupports
  exact filter_mem_sublists _ _

theorem familyUnionSupport_covers
    (n : Nat) (family : List (List Nat))
    (hfaces : ∀ polymer, polymer ∈ family →
      ∀ face, face ∈ polymer → face ∈ physicalFaceEdges n) :
    Covers (familyUnionSupport n family) family := by
  intro face
  rw [mem_familyUnionSupport_iff]
  constructor
  · exact fun h => h.2
  · rintro ⟨polymer, hpolymer, hface⟩
    exact ⟨hfaces polymer hpolymer face hface,
      polymer, hpolymer, hface⟩

/-! ## 2. Decoding corrected Boolean compatibility -/

theorem nodup_of_mem_sublists {A : Type} [DecidableEq A] :
    ∀ (ambient family : List A), ambient.Nodup →
      family ∈ sublists ambient → family.Nodup
  | [], family, _, hfamily => by
      have heq : family = [] := List.mem_singleton.mp hfamily
      rw [heq]
      exact List.nodup_nil
  | head :: tail, family, hnodup, hfamily => by
      rw [sublists_cons'] at hfamily
      rcases List.mem_append.mp hfamily with htail | hhead
      · exact nodup_of_mem_sublists tail family
          (List.nodup_cons.mp hnodup).2 htail
      · obtain ⟨rest, hrest, rfl⟩ := List.mem_map.mp hhead
        apply List.nodup_cons.mpr
        constructor
        · intro hmem
          exact (List.nodup_cons.mp hnodup).1
            (mem_of_mem_sublists tail rest hrest head hmem)
        · exact nodup_of_mem_sublists tail rest
            (List.nodup_cons.mp hnodup).2 hrest

theorem canonicalPolymerCompatibleB_true_invariants
    {n : Nat} {left right : List Nat}
    (hcompatible : canonicalPolymerCompatibleB n left right = true) :
    SupportsDisjoint left right ∧
      SupportsSeparated (faceLinkAdjacentB n) left right := by
  unfold canonicalPolymerCompatibleB at hcompatible
  constructor
  · intro face hleft hright
    have hleftAll := List.all_eq_true.mp hcompatible face hleft
    have hpair := List.all_eq_true.mp hleftAll face hright
    simp at hpair
  · intro leftFace hleft rightFace hright
    have hleftAll := List.all_eq_true.mp hcompatible leftFace hleft
    have hpair := List.all_eq_true.mp hleftAll rightFace hright
    cases hadj : faceLinkAdjacentB n leftFace rightFace with
    | false => rfl
    | true =>
        rw [hadj] at hpair
        simp at hpair

theorem canonicalFamilyCompatibleB_true_invariants (n : Nat) :
    ∀ family : List (List Nat), family.Nodup →
      canonicalFamilyCompatibleB n family = true →
        DistinctDisjoint family ∧
          DistinctSeparated (faceLinkAdjacentB n) family
  | [], _, _ => by
      constructor <;> intro left hleft <;> cases hleft
  | head :: tail, hnodup, hcompatible => by
      have hparts := List.nodup_cons.mp hnodup
      have hbool :
          tail.all (canonicalPolymerCompatibleB n head) = true ∧
            canonicalFamilyCompatibleB n tail = true := by
        simpa [canonicalFamilyCompatibleB] using
          ((Bool.and_eq_true _ _).mp hcompatible)
      have ih := canonicalFamilyCompatibleB_true_invariants n tail
        hparts.2 hbool.2
      have hhead : ∀ component, component ∈ tail →
          SupportsDisjoint head component ∧
            SupportsSeparated (faceLinkAdjacentB n) head component := by
        intro component hcomponent
        exact canonicalPolymerCompatibleB_true_invariants
          (List.all_eq_true.mp hbool.1 component hcomponent)
      constructor
      · intro left hleft right hright hne
        rcases List.mem_cons.mp hleft with heqLeft | hleftTail
        · subst left
          rcases List.mem_cons.mp hright with heqRight | hrightTail
          · subst right
            exact absurd rfl hne
          · exact (hhead right hrightTail).1
        · rcases List.mem_cons.mp hright with heqRight | hrightTail
          · subst right
            exact supportsDisjoint_symm (hhead left hleftTail).1
          · exact ih.1 left hleftTail right hrightTail hne
      · intro left hleft right hright hne
        rcases List.mem_cons.mp hleft with heqLeft | hleftTail
        · subst left
          rcases List.mem_cons.mp hright with heqRight | hrightTail
          · subst right
            exact absurd rfl hne
          · exact (hhead right hrightTail).2
        · rcases List.mem_cons.mp hright with heqRight | hrightTail
          · subst right
            exact supportsSeparated_symm (faceLinkAdjacentB_symmetric n)
              (hhead left hleftTail).2
          · exact ih.2 left hleftTail right hrightTail hne

/-! ## 3. Invariants of a compatible ambient family -/

theorem compatibleAmbientFamily_sublist
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    family ∈ sublists (canonicalSurfacePolymers n) :=
  (List.mem_filter.mp hfamily).1

theorem compatibleAmbientFamily_nodup
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    family.Nodup :=
  nodup_of_mem_sublists (canonicalSurfacePolymers n) family
    (canonicalSurfacePolymers_nodup n)
    (compatibleAmbientFamily_sublist hfamily)

theorem compatibleAmbientFamily_member_ambient
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n)
    {polymer : List Nat} (hpolymer : polymer ∈ family) :
    polymer ∈ canonicalSurfacePolymers n :=
  mem_of_mem_sublists (canonicalSurfacePolymers n) family
    (compatibleAmbientFamily_sublist hfamily) polymer hpolymer

def compatibleAmbientFamily_allNonempty
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    AllNonempty family := by
  intro polymer hpolymer
  exact canonicalSurfacePolymers_allNonempty n polymer
    (compatibleAmbientFamily_member_ambient hfamily hpolymer)

def compatibleAmbientFamily_allConnected
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    AllConnected (faceLinkAdjacentB n) family := by
  intro polymer hpolymer
  exact canonicalSurfacePolymers_allConnected n polymer
    (compatibleAmbientFamily_member_ambient hfamily hpolymer)

theorem compatibleAmbientFamily_member_faceSupport
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n)
    {polymer : List Nat} (hpolymer : polymer ∈ family) :
    polymer ∈ cutoffOneFaceSupports n :=
  canonicalSurfacePolymer_mem_faceSupports
    (compatibleAmbientFamily_member_ambient hfamily hpolymer)

theorem compatibleAmbientFamily_invariants
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    DistinctDisjoint family ∧
      DistinctSeparated (faceLinkAdjacentB n) family :=
  canonicalFamilyCompatibleB_true_invariants n family
    (compatibleAmbientFamily_nodup hfamily)
    (List.mem_filter.mp hfamily).2

theorem compatibleAmbientFamily_union_covers
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    Covers (familyUnionSupport n family) family :=
  familyUnionSupport_covers n family
    (fun polymer hpolymer face hface =>
      mem_of_mem_sublists (physicalFaceEdges n) polymer
        (compatibleAmbientFamily_member_faceSupport hfamily hpolymer)
        face hface)

/-! ## 4. Component uniqueness recovers every compatible family -/

theorem rawSurfaceComponents_equivalent_compatibleFamily
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    FamiliesSupportEquivalent
      (surfaceComponents n
        (componentLabel (familyUnionSupport n family))) family := by
  let support := familyUnionSupport n family
  have hsupport : support ∈ cutoffOneFaceSupports n :=
    familyUnionSupport_mem_cutoffOneFaceSupports n family
  have hexcited := excitedPlaquetteIds_componentLabel_eq_support hsupport
  have hcover : Covers
      (excitedPlaquetteIds n (componentLabel support)) family := by
    intro face
    rw [hexcited]
    exact compatibleAmbientFamily_union_covers hfamily face
  exact surfaceComponents_unique_up_to_support n (componentLabel support)
    hcover
    (compatibleAmbientFamily_allConnected hfamily)
    (compatibleAmbientFamily_allNonempty hfamily)
    (compatibleAmbientFamily_invariants hfamily).2

private theorem canonicalRawComponent_eq_candidate
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n)
    {raw candidate : List Nat}
    (hraw : raw ∈ surfaceComponents n
      (componentLabel (familyUnionSupport n family)))
    (hcandidate : candidate ∈ family)
    (hsame : SameSupport raw candidate) :
    canonicalFaceSupport n raw = candidate := by
  apply sublists_eq_of_mem_iff (physicalFaceEdges n)
    (canonicalFaceSupport n raw) candidate
    (physicalFaceEdges_nodup n)
  · exact canonicalFaceSupport_mem_cutoffOneFaceSupports n raw
  · exact compatibleAmbientFamily_member_faceSupport hfamily hcandidate
  · intro face
    rw [mem_canonicalFaceSupport_iff
      (surfaceComponent_subset_physicalFaceEdges hraw) face]
    exact hsame face

theorem canonicalSurfaceFamily_mem_iff_compatibleFamily
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n)
    (polymer : List Nat) :
    polymer ∈ canonicalSurfaceFamily n (familyUnionSupport n family) ↔
      polymer ∈ family := by
  have hunique := rawSurfaceComponents_equivalent_compatibleFamily hfamily
  constructor
  · intro hpolymer
    unfold canonicalSurfaceFamily at hpolymer
    obtain ⟨raw, hraw, heq⟩ := List.mem_map.mp hpolymer
    obtain ⟨candidate, hcandidate, hsame⟩ := hunique.1 raw hraw
    have hcanonical := canonicalRawComponent_eq_candidate hfamily
      hraw hcandidate hsame
    rw [← heq, hcanonical]
    exact hcandidate
  · intro hpolymer
    obtain ⟨raw, hraw, hsame⟩ := hunique.2 polymer hpolymer
    have hcanonical := canonicalRawComponent_eq_candidate hfamily
      hraw hpolymer (fun face => (hsame face).symm)
    unfold canonicalSurfaceFamily
    exact List.mem_map.mpr ⟨raw, hraw, hcanonical⟩

theorem compatibleAmbientFamily_eq_unionAmbientOrdered
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    ambientOrderedFamily n
        (canonicalSurfaceFamily n (familyUnionSupport n family)) =
      family := by
  have hsupport : familyUnionSupport n family ∈
      cutoffOneFaceSupports n :=
    familyUnionSupport_mem_cutoffOneFaceSupports n family
  have hgas : canonicalSurfaceFamily n (familyUnionSupport n family) ∈
      canonicalConnectedSurfaceGas n := by
    unfold canonicalConnectedSurfaceGas
    exact List.mem_map.mpr
      ⟨familyUnionSupport n family, hsupport, rfl⟩
  apply sublists_eq_of_mem_iff (canonicalSurfacePolymers n)
    (ambientOrderedFamily n
      (canonicalSurfaceFamily n (familyUnionSupport n family)))
    family (canonicalSurfacePolymers_nodup n)
  · unfold ambientOrderedFamily
    exact filter_mem_sublists _ _
  · exact compatibleAmbientFamily_sublist hfamily
  · intro polymer
    rw [gasFamily_mem_ambientOrderedFamily_iff hgas,
      canonicalSurfaceFamily_mem_iff_compatibleFamily hfamily]

theorem mem_compatibleAmbientFamilies_iff_exists_exactGas
    {n : Nat} {family : List (List Nat)} :
    family ∈ canonicalCompatibleAmbientFamilies n ↔
      ∃ exactFamily,
        exactFamily ∈ canonicalConnectedSurfaceGas n ∧
          ambientOrderedFamily n exactFamily = family := by
  constructor
  · intro hfamily
    let exactFamily :=
      canonicalSurfaceFamily n (familyUnionSupport n family)
    have hsupport := familyUnionSupport_mem_cutoffOneFaceSupports n family
    have hgas : exactFamily ∈ canonicalConnectedSurfaceGas n := by
      unfold exactFamily canonicalConnectedSurfaceGas
      exact List.mem_map.mpr
        ⟨familyUnionSupport n family, hsupport, rfl⟩
    exact ⟨exactFamily, hgas,
      compatibleAmbientFamily_eq_unionAmbientOrdered hfamily⟩
  · rintro ⟨exactFamily, hexact, rfl⟩
    exact gasFamily_ambientOrdered_mem_compatibleFamilies hexact

/-! ## 5. Equality of the exact-gas and compatible-family enumeration lists -/

def ambientOrderedExactGas (n : Nat) : List (List (List Nat)) :=
  (canonicalConnectedSurfaceGas n).map (ambientOrderedFamily n)

theorem mem_ambientOrderedExactGas_iff_compatible
    {n : Nat} {family : List (List Nat)} :
    family ∈ ambientOrderedExactGas n ↔
      family ∈ canonicalCompatibleAmbientFamilies n := by
  constructor
  · intro hfamily
    unfold ambientOrderedExactGas at hfamily
    obtain ⟨exactFamily, hexact, heq⟩ := List.mem_map.mp hfamily
    rw [← heq]
    exact gasFamily_ambientOrdered_mem_compatibleFamilies hexact
  · intro hfamily
    obtain ⟨exactFamily, hexact, heq⟩ :=
      mem_compatibleAmbientFamilies_iff_exists_exactGas.mp hfamily
    unfold ambientOrderedExactGas
    exact List.mem_map.mpr ⟨exactFamily, hexact, heq⟩

theorem canonicalCompatibleAmbientFamilies_nodup (n : Nat) :
    (canonicalCompatibleAmbientFamilies n).Nodup := by
  unfold canonicalCompatibleAmbientFamilies
  exact List.filter_sublist.nodup
    (sublists_nodup (canonicalSurfacePolymers n)
      (canonicalSurfacePolymers_nodup n))

theorem ambientOrderedFamily_injective_on_exactGas
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalConnectedSurfaceGas n)
    (hright : right ∈ canonicalConnectedSurfaceGas n)
    (heq : ambientOrderedFamily n left =
      ambientOrderedFamily n right) :
    left = right := by
  obtain ⟨leftSupport, hleftSupport, hleftEq⟩ := List.mem_map.mp hleft
  obtain ⟨rightSupport, hrightSupport, hrightEq⟩ :=
    List.mem_map.mp hright
  have hmembers : ∀ polymer,
      polymer ∈ canonicalSurfaceFamily n leftSupport ↔
        polymer ∈ canonicalSurfaceFamily n rightSupport := by
    intro polymer
    constructor
    · intro hpolymer
      have hpolymerLeft : polymer ∈ left := by
        rw [← hleftEq]
        exact hpolymer
      have horderedLeft : polymer ∈ ambientOrderedFamily n left :=
        (gasFamily_mem_ambientOrderedFamily_iff hleft polymer).2
          hpolymerLeft
      rw [heq] at horderedLeft
      have hpolymerRight : polymer ∈ right :=
        (gasFamily_mem_ambientOrderedFamily_iff hright polymer).1
          horderedLeft
      rw [← hrightEq] at hpolymerRight
      exact hpolymerRight
    · intro hpolymer
      have hpolymerRight : polymer ∈ right := by
        rw [← hrightEq]
        exact hpolymer
      have horderedRight : polymer ∈ ambientOrderedFamily n right :=
        (gasFamily_mem_ambientOrderedFamily_iff hright polymer).2
          hpolymerRight
      rw [← heq] at horderedRight
      have hpolymerLeft : polymer ∈ left :=
        (gasFamily_mem_ambientOrderedFamily_iff hleft polymer).1
          horderedRight
      rw [← hleftEq] at hpolymerLeft
      exact hpolymerLeft
  have hsupportEq : leftSupport = rightSupport := by
    apply sublists_eq_of_mem_iff (physicalFaceEdges n)
      leftSupport rightSupport (physicalFaceEdges_nodup n)
      hleftSupport hrightSupport
    intro face
    rw [canonicalSurfaceFamily_covers hleftSupport face,
      canonicalSurfaceFamily_covers hrightSupport face]
    constructor
    · rintro ⟨polymer, hpolymer, hface⟩
      exact ⟨polymer, (hmembers polymer).1 hpolymer, hface⟩
    · rintro ⟨polymer, hpolymer, hface⟩
      exact ⟨polymer, (hmembers polymer).2 hpolymer, hface⟩
  exact hleftEq.symm.trans
    ((congrArg (canonicalSurfaceFamily n) hsupportEq).trans hrightEq)

theorem ambientOrderedExactGas_nodup (n : Nat) :
    (ambientOrderedExactGas n).Nodup := by
  unfold ambientOrderedExactGas
  apply nodup_map_of_injOn (ambientOrderedFamily n)
    (canonicalConnectedSurfaceGas n)
    (canonicalConnectedSurfaceGas_nodup n)
  intro left hleft right hright
  exact ambientOrderedFamily_injective_on_exactGas hleft hright

theorem ambientOrderedExactGas_perm_compatibleFamilies (n : Nat) :
    (ambientOrderedExactGas n).Perm
      (canonicalCompatibleAmbientFamilies n) := by
  apply perm_of_nodup_mem_iff
    (ambientOrderedExactGas n)
    (canonicalCompatibleAmbientFamilies n)
    (ambientOrderedExactGas_nodup n)
    (canonicalCompatibleAmbientFamilies_nodup n)
  intro family
  exact mem_ambientOrderedExactGas_iff_compatible

/-! ## 6. Exact equality of the physical and corrected polymer partitions -/

def parametricCanonicalCompatibleAmbientPartition
    (w : Q') (n : Nat) : Q' :=
  listQSum (canonicalSurfaceFamilyActivity w n)
    (canonicalCompatibleAmbientFamilies n)

def parametricAmbientOrderedExactGasPartition
    (w : Q') (n : Nat) : Q' :=
  listQSum (canonicalSurfaceFamilyActivity w n)
    (ambientOrderedExactGas n)

private theorem listQSum_map_eqv_local {A B : Type}
    (f : A → Q') (g : B → Q') (reindex : A → B) :
    ∀ xs : List A,
      (∀ item, item ∈ xs → f item ≈ g (reindex item)) →
      listQSum f xs ≈ listQSum g (xs.map reindex)
  | [], _ => Q'.eqv_refl 0
  | head :: tail, h => by
      change f head + listQSum f tail ≈
        g (reindex head) + listQSum g (tail.map reindex)
      exact Q'.add_eqv_congr'
        (h head List.mem_cons_self)
        (listQSum_map_eqv_local f g reindex tail
          (fun item hitem =>
            h item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_swap_local {A : Type} (f : A → Q')
    (first second : A) (rest : List A) :
    listQSum f (second :: first :: rest) ≈
      listQSum f (first :: second :: rest) := by
  change f second + (f first + listQSum f rest) ≈
    f first + (f second + listQSum f rest)
  refine Q'.eqv_trans _ ((f second + f first) + listQSum f rest) _
    (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ ((f first + f second) + listQSum f rest) _
    (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)) ?_
  exact Q'.add_assoc_eqv _ _ _

theorem listQSum_perm {A : Type} (f : A → Q') :
    ∀ {left right : List A}, left.Perm right →
      listQSum f left ≈ listQSum f right
  | _, _, List.Perm.nil => Q'.eqv_refl 0
  | _, _, List.Perm.cons _ hperm =>
      Q'.add_eqv_congr_left _ _ _ (listQSum_perm f hperm)
  | _, _, List.Perm.swap first second rest =>
      listQSum_swap_local f first second rest
  | _, _, List.Perm.trans first second =>
      Q'.eqv_trans _ _ _
        (listQSum_perm f first) (listQSum_perm f second)

theorem parametricConnectedSurfaceGasPartition_eqv_ambientOrdered
    (w : Q') (n : Nat) :
    parametricCanonicalConnectedSurfaceGasPartition w n ≈
      parametricAmbientOrderedExactGasPartition w n := by
  unfold parametricCanonicalConnectedSurfaceGasPartition
    parametricAmbientOrderedExactGasPartition ambientOrderedExactGas
  apply listQSum_map_eqv_local
  intro family hfamily
  exact gasFamilyActivity_eqv_ambientOrdered w hfamily

theorem parametricAmbientOrderedPartition_eqv_compatibleAmbient
    (w : Q') (n : Nat) :
    parametricAmbientOrderedExactGasPartition w n ≈
      parametricCanonicalCompatibleAmbientPartition w n := by
  unfold parametricAmbientOrderedExactGasPartition
    parametricCanonicalCompatibleAmbientPartition
  exact listQSum_perm (canonicalSurfaceFamilyActivity w n)
    (ambientOrderedExactGas_perm_compatibleFamilies n)

theorem parametricLocalizedSpinFoamPartition_eq_correctedPolymerPartition
    (w : Q') (n : Nat) :
    parametricLocalizedSpinFoamPartition w n ≈
      parametricCanonicalCompatibleAmbientPartition w n := by
  exact Q'.eqv_trans _ _ _
    (parametricLocalizedSpinFoamPartition_eq_connectedSurfaceGas w n)
    (Q'.eqv_trans _ _ _
      (parametricConnectedSurfaceGasPartition_eqv_ambientOrdered w n)
      (parametricAmbientOrderedPartition_eqv_compatibleAmbient w n))

end YMGap.Continuum.Z4CanonicalPolymerRange

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalPolymerRange.nodup_of_mem_sublists
#print axioms YMGap.Continuum.Z4CanonicalPolymerRange.canonicalFamilyCompatibleB_true_invariants
#print axioms YMGap.Continuum.Z4CanonicalPolymerRange.rawSurfaceComponents_equivalent_compatibleFamily
#print axioms YMGap.Continuum.Z4CanonicalPolymerRange.canonicalSurfaceFamily_mem_iff_compatibleFamily
#print axioms YMGap.Continuum.Z4CanonicalPolymerRange.compatibleAmbientFamily_eq_unionAmbientOrdered
#print axioms YMGap.Continuum.Z4CanonicalPolymerRange.mem_compatibleAmbientFamilies_iff_exists_exactGas
#print axioms YMGap.Continuum.Z4CanonicalPolymerRange.ambientOrderedExactGas_perm_compatibleFamilies
#print axioms YMGap.Continuum.Z4CanonicalPolymerRange.listQSum_perm
#print axioms YMGap.Continuum.Z4CanonicalPolymerRange.parametricLocalizedSpinFoamPartition_eq_correctedPolymerPartition
