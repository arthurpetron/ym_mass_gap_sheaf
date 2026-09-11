/-
# Constructing the two-face inward-mate order at a physical link

The arbitrary-order inward-mate compiler consumes two `List.Perm` witnesses.
This file constructs them from the actual finite-box incident-plaquette ID
list.  Two distinct incident IDs are moved to the first two slots; duplicate
freeness proves that neither occurs in the residual list.  Consequently the
two-face mate labelling changes exactly the exposed slots and leaves the same
residual spin word on both sides.

The result feeds those witnesses into the production SU(2) multiplicity
inequality.  The remaining geometric step is to identify, for every boundary
link of the selected cube, the two incident cube-face IDs and prove that the
other four changed cube faces are absent from that link.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or trusted external computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionReordering
import YMGap.Continuum.Z4LinkIdentifierFreshness
import YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateIncidentOrder

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionReordering
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality

/-- Change exactly two physical plaquette coordinates by the even inward-mate
label map.  Cube geometry will later identify these coordinates with the two
selected faces incident on one boundary link. -/
def twoFaceEvenInwardMatePhysical
    (leftId rightId : Nat) (physical : EdgeLabelling) : EdgeLabelling :=
  fun faceId =>
    if faceId = leftId then evenInwardMateLabel (physical faceId)
    else if faceId = rightId then evenInwardMateLabel (physical faceId)
    else physical faceId

theorem twoFaceEvenInwardMatePhysical_left
    (leftId rightId : Nat) (physical : EdgeLabelling) :
    twoFaceEvenInwardMatePhysical leftId rightId physical leftId =
      evenInwardMateLabel (physical leftId) := by
  simp [twoFaceEvenInwardMatePhysical]

theorem twoFaceEvenInwardMatePhysical_right
    {leftId rightId : Nat} (physical : EdgeLabelling)
    (hne : leftId ≠ rightId) :
    twoFaceEvenInwardMatePhysical leftId rightId physical rightId =
      evenInwardMateLabel (physical rightId) := by
  simp [twoFaceEvenInwardMatePhysical, hne.symm]

theorem twoFaceEvenInwardMatePhysical_of_ne
    {leftId rightId faceId : Nat} (physical : EdgeLabelling)
    (hleft : faceId ≠ leftId) (hright : faceId ≠ rightId) :
    twoFaceEvenInwardMatePhysical leftId rightId physical faceId =
      physical faceId := by
  simp [twoFaceEvenInwardMatePhysical, hleft, hright]

/-- Constructively move two distinct members of a list to its first two
slots.  The residual list is an explicit witness, not a choice-extracted
permutation representative. -/
theorem exists_two_head_perm_of_mem
    {A : Type} {left right : A} {items : List A}
    (hleft : left ∈ items) (hright : right ∈ items)
    (hne : left ≠ right) :
    ∃ rest : List A, items.Perm (left :: right :: rest) := by
  obtain ⟨beforeLeft, afterLeft, hsplitLeft⟩ :=
    List.append_of_mem hleft
  subst items
  have hrightRest : right ∈ beforeLeft ++ afterLeft := by
    rcases List.mem_append.mp hright with hbefore | hafter
    · exact List.mem_append_left _ hbefore
    · rcases List.mem_cons.mp hafter with heq | htail
      · exact False.elim (hne heq.symm)
      · exact List.mem_append_right _ htail
  obtain ⟨beforeRight, afterRight, hsplitRight⟩ :=
    List.append_of_mem hrightRest
  refine ⟨beforeRight ++ afterRight, ?_⟩
  have hleftFront :
      (beforeLeft ++ left :: afterLeft).Perm
        (left :: beforeLeft ++ afterLeft) :=
    List.perm_middle
  have hrightFront :
      (beforeLeft ++ afterLeft).Perm
        (right :: beforeRight ++ afterRight) := by
    rw [hsplitRight]
    exact List.perm_middle
  exact hleftFront.trans (List.Perm.cons left hrightFront)

/-- Duplicate freeness turns a two-head permutation into the two exclusion
facts needed to prove that the residual spin word is unchanged by the mate. -/
theorem two_head_perm_rest_excludes
    {A : Type} {left right : A} {items rest : List A}
    (hnodup : items.Nodup)
    (hperm : items.Perm (left :: right :: rest)) :
    left ∉ rest ∧ right ∉ rest := by
  have hfront : (left :: right :: rest).Nodup := hperm.nodup hnodup
  have hleft := List.nodup_cons.mp hfront
  have hright := List.nodup_cons.mp hleft.2
  exact ⟨fun hmem => hleft.1 (List.mem_cons_of_mem right hmem), hright.1⟩

/-- **Actual incident-list permutation witnesses.**  Two distinct numerical
plaquette IDs incident on the same finite-box link determine one common
residual spin word.  The source incident word exposes the two source spins;
the exact two-face mate incident word exposes their mates and retains that
same residual word. -/
theorem incidentPhysicalSpins_twoFace_permutations
    (n : Nat)
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link)
    (leftId rightId : Nat)
    (physical : EdgeLabelling)
    (hleft : leftId ∈ incidentPlaqIds n link)
    (hright : rightId ∈ incidentPlaqIds n link)
    (hne : leftId ≠ rightId) :
    ∃ rest : List Nat,
      (incidentPhysicalSpins n link physical).Perm
        (physical leftId :: physical rightId :: rest) ∧
      (incidentPhysicalSpins n link
          (twoFaceEvenInwardMatePhysical leftId rightId physical)).Perm
        (evenInwardMateLabel (physical leftId) ::
          evenInwardMateLabel (physical rightId) :: rest) := by
  obtain ⟨restIds, hids⟩ :=
    exists_two_head_perm_of_mem hleft hright hne
  have hexcludes := two_head_perm_rest_excludes
    (incidentPlaqIds_nodup n link) hids
  have hrestMate :
      restIds.map (twoFaceEvenInwardMatePhysical leftId rightId physical) =
        restIds.map physical := by
    apply List.map_congr_left
    intro faceId hface
    apply twoFaceEvenInwardMatePhysical_of_ne
    · intro heq
      subst faceId
      exact hexcludes.1 hface
    · intro heq
      subst faceId
      exact hexcludes.2 hface
  refine ⟨restIds.map physical, ?_, ?_⟩
  · simpa only [incidentPhysicalSpins, List.map_cons] using hids.map physical
  · have hmate := hids.map
      (twoFaceEvenInwardMatePhysical leftId rightId physical)
    simpa only [incidentPhysicalSpins, List.map_cons,
      twoFaceEvenInwardMatePhysical_left,
      twoFaceEvenInwardMatePhysical_right physical hne,
      hrestMate] using hmate

/-- **Incident-link multiplicity compiler.**  The two concrete membership
witnesses now supply every list-ordering input required by the local inward
mate theorem.  The output retains the one explicit stretched continuation;
no global strand rerouting is asserted here. -/
theorem incidentPhysicalSpins_twoFace_inwardMate_le_add_stretched
    (K n : Nat)
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link)
    (leftId rightId : Nat)
    (physical : EdgeLabelling)
    (hK : 1 ≤ K)
    (hleft : leftId ∈ incidentPlaqIds n link)
    (hright : rightId ∈ incidentPlaqIds n link)
    (hne : leftId ≠ rightId)
    (hbounded : SpinsBounded K (incidentPhysicalSpins n link physical)) :
    ∃ rest : List Nat,
      (incidentPhysicalSpins n link physical).Perm
        (physical leftId :: physical rightId :: rest) ∧
      (incidentPhysicalSpins n link
          (twoFaceEvenInwardMatePhysical leftId rightId physical)).Perm
        (evenInwardMateLabel (physical leftId) ::
          evenInwardMateLabel (physical rightId) :: rest) ∧
      explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          (incidentPhysicalSpins n link physical).length
          (externalSpinsOfList (incidentPhysicalSpins n link physical)) ≤
        explicitValenceMultiplicity (linkAuxiliaryCutoff K)
            (incidentPhysicalSpins n link
              (twoFaceEvenInwardMatePhysical
                leftId rightId physical)).length
            (externalSpinsOfList
              (incidentPhysicalSpins n link
                (twoFaceEvenInwardMatePhysical
                  leftId rightId physical))) +
          explicitValenceMultiplicity (linkAuxiliaryCutoff K)
            ((physical leftId + physical rightId) :: rest).length
            (externalSpinsOfList
              ((physical leftId + physical rightId) :: rest)) := by
  obtain ⟨rest, hsource, hmate⟩ :=
    incidentPhysicalSpins_twoFace_permutations
      n link leftId rightId physical hleft hright hne
  have hlengthSource :
      (incidentPhysicalSpins n link physical).length ≤ 6 := by
    simpa only [incidentPhysicalSpins, List.length_map] using
      incidentPlaqIds_length_le_six n link
  have hlengthFront :
      (physical leftId :: physical rightId :: rest).length ≤ 6 := by
    rw [← hsource.length_eq]
    exact hlengthSource
  have hboundedFront :
      SpinsBounded K (physical leftId :: physical rightId :: rest) :=
    spinsBounded_of_perm hsource hbounded
  refine ⟨rest, hsource, hmate, ?_⟩
  exact explicitValenceMultiplicity_physical_inwardMate_of_permutations
    K (physical leftId) (physical rightId) rest
    (incidentPhysicalSpins n link physical)
    (incidentPhysicalSpins n link
      (twoFaceEvenInwardMatePhysical leftId rightId physical))
    hK hlengthFront hboundedFront hsource hmate

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateIncidentOrder

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateIncidentOrder.exists_two_head_perm_of_mem
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateIncidentOrder.incidentPhysicalSpins_twoFace_permutations
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateIncidentOrder.incidentPhysicalSpins_twoFace_inwardMate_le_add_stretched
