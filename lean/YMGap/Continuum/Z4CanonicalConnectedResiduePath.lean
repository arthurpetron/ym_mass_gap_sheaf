/-
# Simple-path payment for the canonical connected residue

Every source pair left after recoverable switching has a disagreement
component joining the marked polymer to a polymer leaving the smaller box.
The Warshall certificate is constructively loop-erased.  Its distinct
polymers occur in one of the two source replicas, so their total plaquette
count is charged at most once to the pair activity.
-/

import YMGap.Continuum.FiniteSimpleWalk
import YMGap.Continuum.Z4CanonicalBoundarySwitchSummation

namespace YMGap.Continuum.Z4CanonicalConnectedResiduePath

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteDisagreementReverseRecovery
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery
open YMGap.Continuum.Z4CanonicalBoundarySwitchSummation
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalIncompatibilityWalk
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

abbrev PolymerFamily := List (List Nat)

def sourceDisagreementEdge {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (pair : SourcePair small n root) :
    CanonicalAtom n → CanonicalAtom n → Bool :=
  disagreementEdge (canonicalAmbientAtoms n)
    (canonicalAtomCompatibleB n)
    (memberB (canonicalFamilyAtoms (sourceLeftCompatible pair)))
    (memberB (canonicalFamilyAtoms
      (sourceRightCompatible hsmall pair)))

theorem connectedSourcePair_reach_true
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : SourcePair small n root)
    (hpair : pair ∈ connectedSourcePairs hsmall) :
    boundaryOutsideDisagreementReachB small
      (sourceLeftCompatible pair)
      (sourceRightCompatible hsmall pair)
      (sourceRootAtom pair) = true := by
  have htest := (List.mem_filter.mp hpair).2
  unfold sourceSeparatedB at htest
  cases hreach : boundaryOutsideDisagreementReachB small
      (sourceLeftCompatible pair)
      (sourceRightCompatible hsmall pair)
      (sourceRootAtom pair) <;> simp_all

theorem connectedSourcePair_has_outside_reach
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : SourcePair small n root)
    (hpair : pair ∈ connectedSourcePairs hsmall) :
    ∃ outside : CanonicalAtom n,
      outside.val ∈ pair.1.val ∧
        polymerInsideBoxB small n outside.val = false ∧
          canonicalDisagreementCut
            (sourceLeftCompatible pair)
            (sourceRightCompatible hsmall pair)
            (sourceRootAtom pair) outside = true := by
  have hreach := connectedSourcePair_reach_true hsmall pair hpair
  unfold boundaryOutsideDisagreementReachB at hreach
  obtain ⟨outside, houtsideAtoms, hterm⟩ := List.any_eq_true.mp hreach
  have hparts := (Bool.and_eq_true _ _).mp hterm
  have houtsideBox : polymerInsideBoxB small n outside.val = false := by
    cases hinside : polymerInsideBoxB small n outside.val <;>
      simp_all
  exact ⟨outside,
    (canonicalFamilyAtom_mem_iff (sourceLeftCompatible pair) outside).1
      houtsideAtoms,
    houtsideBox, hparts.2⟩

def sourceSimpleDisagreementPath
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : SourcePair small n root) (outside : CanonicalAtom n)
    (hreaches : canonicalDisagreementCut
      (sourceLeftCompatible pair)
      (sourceRightCompatible hsmall pair)
      (sourceRootAtom pair) outside = true) :
    CWalk.Simple (sourceDisagreementEdge hsmall pair)
      (sourceRootAtom pair) outside :=
  simpleWalkOfWarshall (sourceDisagreementEdge hsmall pair)
    (canonicalAmbientAtoms n) (sourceRootAtom pair) outside hreaches

def atomFaceCount {n : Nat} (atoms : List (CanonicalAtom n)) : Nat :=
  listNatWeight (fun atom => atom.val.length) atoms

theorem atomFaceCount_append {n : Nat}
    (first second : List (CanonicalAtom n)) :
    atomFaceCount (first ++ second) =
      atomFaceCount first + atomFaceCount second :=
  listNatWeight_append _ first second

theorem atomFaceCount_canonicalFamilyAtoms
    {n : Nat} {family : PolymerFamily}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    atomFaceCount (canonicalFamilyAtoms hfamily) =
      familyFaceCount family := by
  unfold atomFaceCount
  rw [← listNatWeight_map Subtype.val List.length
    (canonicalFamilyAtoms hfamily)]
  rw [canonicalFamilyAtoms_values hfamily]
  clear hfamily
  induction family with
  | nil => rfl
  | cons polymer rest ih =>
      change polymer.length + listNatWeight List.length rest =
        polymer.length + familyFaceCount rest
      rw [ih]

theorem sourceDisagreementEdge_target_memberB
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : SourcePair small n root)
    {first second : CanonicalAtom n}
    (hedge : sourceDisagreementEdge hsmall pair first second = true) :
    memberB (canonicalFamilyAtoms (sourceLeftCompatible pair)) second = true ∨
      memberB (canonicalFamilyAtoms
        (sourceRightCompatible hsmall pair)) second = true := by
  have hbits := (Bool.and_eq_true _ _).mp hedge |>.2
  unfold sourceDisagreementEdge disagreementBits leftOnly rightOnly at hbits
  cases hleftFirst : memberB
      (canonicalFamilyAtoms (sourceLeftCompatible pair)) first <;>
    cases hrightFirst : memberB
      (canonicalFamilyAtoms (sourceRightCompatible hsmall pair)) first <;>
    cases hleftSecond : memberB
      (canonicalFamilyAtoms (sourceLeftCompatible pair)) second <;>
    cases hrightSecond : memberB
      (canonicalFamilyAtoms (sourceRightCompatible hsmall pair)) second <;>
    simp_all

theorem sourceSimpleDisagreementPath_vertices_mem_pair
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : SourcePair small n root) (outside : CanonicalAtom n)
    (hreaches : canonicalDisagreementCut
      (sourceLeftCompatible pair)
      (sourceRightCompatible hsmall pair)
      (sourceRootAtom pair) outside = true) :
    ∀ atom,
      atom ∈ (sourceSimpleDisagreementPath hsmall pair outside
        hreaches).walk.vertices →
      atom ∈ canonicalFamilyAtoms (sourceLeftCompatible pair) ++
        canonicalFamilyAtoms (sourceRightCompatible hsmall pair) := by
  let path := sourceSimpleDisagreementPath hsmall pair outside hreaches
  have hrootMem : sourceRootAtom pair ∈
      canonicalFamilyAtoms (sourceLeftCompatible pair) :=
    (canonicalFamilyAtom_mem_iff
      (sourceLeftCompatible pair) (sourceRootAtom pair)).2
      (sourceRootMem pair)
  have hrootB : memberB
      (canonicalFamilyAtoms (sourceLeftCompatible pair))
      (sourceRootAtom pair) = true :=
    (memberB_eq_true_iff _ _).2 hrootMem
  have hall := CWalk.all_vertices_of_start
    (fun atom =>
      memberB (canonicalFamilyAtoms (sourceLeftCompatible pair)) atom = true ∨
        memberB (canonicalFamilyAtoms
          (sourceRightCompatible hsmall pair)) atom = true)
    (fun _ _ hedge _ =>
      sourceDisagreementEdge_target_memberB hsmall pair hedge)
    path.walk (Or.inl hrootB)
  intro atom hatom
  rcases hall atom hatom with hleft | hright
  · exact List.mem_append_left _ ((memberB_eq_true_iff _ _).1 hleft)
  · exact List.mem_append_right _ ((memberB_eq_true_iff _ _).1 hright)

theorem sourceSimpleDisagreementPath_faceCount_le_pair
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : SourcePair small n root) (outside : CanonicalAtom n)
    (hreaches : canonicalDisagreementCut
      (sourceLeftCompatible pair)
      (sourceRightCompatible hsmall pair)
      (sourceRootAtom pair) outside = true) :
    atomFaceCount
        (sourceSimpleDisagreementPath hsmall pair outside hreaches).walk.vertices
      ≤ familyFaceCount pair.1.val + familyFaceCount pair.2.val := by
  let path := sourceSimpleDisagreementPath hsmall pair outside hreaches
  have hbound : atomFaceCount path.walk.vertices ≤
      atomFaceCount
        (canonicalFamilyAtoms (sourceLeftCompatible pair) ++
          canonicalFamilyAtoms (sourceRightCompatible hsmall pair)) :=
    listNatWeight_le_of_nodup_mem
      (fun atom : CanonicalAtom n => atom.val.length)
      path.walk.vertices
      (canonicalFamilyAtoms (sourceLeftCompatible pair) ++
        canonicalFamilyAtoms (sourceRightCompatible hsmall pair))
      path.nodup
      (sourceSimpleDisagreementPath_vertices_mem_pair
        hsmall pair outside hreaches)
  rw [atomFaceCount_append,
    atomFaceCount_canonicalFamilyAtoms (sourceLeftCompatible pair),
    atomFaceCount_canonicalFamilyAtoms
      (sourceRightCompatible hsmall pair)] at hbound
  simpa [path] using hbound

theorem disagreementCWalk_faceCount_floor
    {n : Nat} {left right : PolymerFamily}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n) :
    ∀ {first last : CanonicalAtom n}
      (walk : CWalk
        (disagreementEdge (canonicalAmbientAtoms n)
          (canonicalAtomCompatibleB n)
          (memberB (canonicalFamilyAtoms hleft))
          (memberB (canonicalFamilyAtoms hright))) first last)
      {start finish : Nat},
      start ∈ first.val → finish ∈ last.val →
        linfDist (boxPlaquetteAt n start) (boxPlaquetteAt n finish) + 1 ≤
          atomFaceCount walk.vertices
  | _, _, .single atom, start, finish, hstart, hfinish => by
      unfold atomFaceCount listNatWeight
      exact canonicalSurfacePolymer_linf_size_floor
        atom.property hstart
        (List.mem_map.mpr ⟨finish, hfinish, rfl⟩)
        (Nat.le_refl _)
  | first, last, .cons hedge rest, start, finish, hstart, hfinish => by
      have hincompatible := canonicalDisagreementEdge_incompatible
        hleft hright hedge
      obtain ⟨leftContact, hleftContact, rightContact,
          hrightContact, hcontact⟩ :=
        canonicalPolymer_incompatible_contact hincompatible
      have hhead :
          linfDist (boxPlaquetteAt n start)
              (boxPlaquetteAt n leftContact) + 1 ≤ first.val.length :=
        canonicalSurfacePolymer_linf_size_floor
          first.property hstart
          (List.mem_map.mpr ⟨leftContact, hleftContact, rfl⟩)
          (Nat.le_refl _)
      have hedgeDist := incompatible_contact_linfDist_le_one hcontact
      have htail := disagreementCWalk_faceCount_floor hleft hright
        rest hrightContact hfinish
      have htriFirst :
          linfDist (boxPlaquetteAt n start)
              (boxPlaquetteAt n rightContact) ≤
            linfDist (boxPlaquetteAt n start)
                (boxPlaquetteAt n leftContact) +
              linfDist (boxPlaquetteAt n leftContact)
                (boxPlaquetteAt n rightContact) := by
        exact z4SepLinf.dist_triangle
          (boxPlaquetteAt n start)
          (boxPlaquetteAt n leftContact)
          (boxPlaquetteAt n rightContact)
      have htriSecond :
          linfDist (boxPlaquetteAt n start)
              (boxPlaquetteAt n finish) ≤
            linfDist (boxPlaquetteAt n start)
                (boxPlaquetteAt n rightContact) +
              linfDist (boxPlaquetteAt n rightContact)
                (boxPlaquetteAt n finish) := by
        exact z4SepLinf.dist_triangle
          (boxPlaquetteAt n start)
          (boxPlaquetteAt n rightContact)
          (boxPlaquetteAt n finish)
      change linfDist (boxPlaquetteAt n start)
          (boxPlaquetteAt n finish) + 1 ≤
        first.val.length + atomFaceCount rest.vertices
      omega

theorem sourceSimpleDisagreementPath_boundary_floor
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : SourcePair small n root) (outside : CanonicalAtom n)
    (hreaches : canonicalDisagreementCut
      (sourceLeftCompatible pair)
      (sourceRightCompatible hsmall pair)
      (sourceRootAtom pair) outside = true)
    {start inner distance : Nat}
    (houtside : polymerInsideBoxB small n outside.val = false)
    (hstart : start ∈ root)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    distance + 2 ≤ atomFaceCount
      (sourceSimpleDisagreementPath hsmall pair outside hreaches).walk.vertices := by
  obtain ⟨outsidePlaquette, houtsidePlaquette, houtsideSmall⟩ :=
    polymerInsideBoxB_false_witness houtside
  obtain ⟨finish, hfinish, hfinishEq⟩ :=
    List.mem_map.mp houtsidePlaquette
  have hfinishOutside :
      boxPlaquetteAt n finish ∉ boxPlaquettes small := by
    rw [hfinishEq]
    exact houtsideSmall
  have houtSmall : outsideBoxB small (boxPlaquetteAt n finish) = true :=
    (outsideBoxB_true_iff_not_mem small (boxPlaquetteAt n finish)).2
      hfinishOutside
  have houtExpanded :
      outsideBoxB (inner + distance) (boxPlaquetteAt n finish) = true := by
    rw [hbox]
    exact houtSmall
  have hsep := outside_expanded_box_linf_floor hstartInner houtExpanded
  have hcost := disagreementCWalk_faceCount_floor
    (sourceLeftCompatible pair) (sourceRightCompatible hsmall pair)
    (sourceSimpleDisagreementPath hsmall pair outside hreaches).walk
    hstart hfinish
  have hcost' :
      linfDist (boxPlaquetteAt n start) (boxPlaquetteAt n finish) + 1 ≤
        atomFaceCount
          (sourceSimpleDisagreementPath hsmall pair outside
            hreaches).walk.vertices := by
    simpa [sourceDisagreementEdge] using hcost
  omega

/-- Every connected source pair pays the full local-to-boundary distance in
distinct source-polymer plaquettes. -/
theorem connectedSourcePair_totalFaceCount_floor
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : SourcePair small n root)
    (hpair : pair ∈ connectedSourcePairs hsmall)
    {start inner distance : Nat}
    (hstart : start ∈ root)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    distance + 2 ≤
      familyFaceCount pair.1.val + familyFaceCount pair.2.val := by
  obtain ⟨outside, _houtsideMem, houtside, hreaches⟩ :=
    connectedSourcePair_has_outside_reach hsmall pair hpair
  exact Nat.le_trans
    (sourceSimpleDisagreementPath_boundary_floor hsmall pair outside
      hreaches houtside hstart hstartInner hbox)
    (sourceSimpleDisagreementPath_faceCount_le_pair
      hsmall pair outside hreaches)

theorem sourcePairWeight_le_totalFacePow
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : SourcePair small n root) :
    sourcePairWeight pair ≤
      anchorPerFaceEnvelope ^
        (familyFaceCount pair.1.val + familyFaceCount pair.2.val) := by
  have hleft := compatibleFamily_activity_le_totalFacePow
    (sourceLeftCompatible pair)
  have hright := compatibleFamily_activity_le_totalFacePow
    (sourceRightCompatible hsmall pair)
  have hright0 := canonicalSurfaceFamilyActivity_nonnegative n pair.2.val
  have hleftPow0 : (0 : Q') ≤
      anchorPerFaceEnvelope ^ familyFaceCount pair.1.val :=
    Q'.pow_nonneg anchorPerFaceEnvelope (by decide)
      (familyFaceCount pair.1.val)
  have hfirst :
      canonicalSurfaceFamilyActivity anchorCoupling n pair.1.val *
          canonicalSurfaceFamilyActivity anchorCoupling n pair.2.val ≤
        anchorPerFaceEnvelope ^ familyFaceCount pair.1.val *
          canonicalSurfaceFamilyActivity anchorCoupling n pair.2.val :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hleft hright0
  have hsecond :
      anchorPerFaceEnvelope ^ familyFaceCount pair.1.val *
          canonicalSurfaceFamilyActivity anchorCoupling n pair.2.val ≤
        anchorPerFaceEnvelope ^ familyFaceCount pair.1.val *
          anchorPerFaceEnvelope ^ familyFaceCount pair.2.val :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hright hleftPow0
  unfold sourcePairWeight
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.pow_add_eqv anchorPerFaceEnvelope
            (familyFaceCount pair.1.val)
            (familyFaceCount pair.2.val)))))

/-- Pointwise geometric decay of every connected residue entry.  This theorem
does not sum the entries; the remaining component/Penrose step must control
their multiplicity without a volume factor. -/
theorem connectedSourcePair_weight_le_boundaryPow
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : SourcePair small n root)
    (hpair : pair ∈ connectedSourcePairs hsmall)
    {start inner distance : Nat}
    (hstart : start ∈ root)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    sourcePairWeight pair ≤
      anchorPerFaceEnvelope ^ (distance + 2) := by
  have htotal := connectedSourcePair_totalFaceCount_floor
    hsmall pair hpair hstart hstartInner hbox
  exact Q'.le_trans' _ _ _
    (sourcePairWeight_le_totalFacePow hsmall pair)
    (YMGap.Continuum.HKConvGen.pow_base_antitone
      (r := anchorPerFaceEnvelope) (by decide) (by decide) htotal)

end YMGap.Continuum.Z4CanonicalConnectedResiduePath

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalConnectedResiduePath.connectedSourcePair_reach_true
#print axioms YMGap.Continuum.Z4CanonicalConnectedResiduePath.sourceSimpleDisagreementPath_faceCount_le_pair
#print axioms YMGap.Continuum.Z4CanonicalConnectedResiduePath.disagreementCWalk_faceCount_floor
#print axioms YMGap.Continuum.Z4CanonicalConnectedResiduePath.connectedSourcePair_totalFaceCount_floor
#print axioms YMGap.Continuum.Z4CanonicalConnectedResiduePath.sourcePairWeight_le_totalFacePow
#print axioms YMGap.Continuum.Z4CanonicalConnectedResiduePath.connectedSourcePair_weight_le_boundaryPow
