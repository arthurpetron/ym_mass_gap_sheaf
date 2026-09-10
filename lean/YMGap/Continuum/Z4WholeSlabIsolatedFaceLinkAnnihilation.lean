/-
# An isolated nonzero coarse face is annihilated by a whole-slab link

The whole corrected-slab recoupling kernel uses a valence-zero-through-six
production multiplicity at every coarse link.  This file proves the exact
local compiler needed for an isolated dyadic pair bubble: if one incident
coarse face has nonzero retained spin and every other incident face has spin
zero, then that production multiplicity is zero.  Hence the complete slab
link product is zero whenever the selected link belongs to its carrier.

The proof does not enumerate spin assignments.  It extracts the selected
singleton from the duplicate-free incident-face list, recognizes the full
incident word as a zero extension, and reduces the production resolver to
the one-valent vacuum multiplicity.

This is link algebra only.  It does not yet select an incident link for an
arbitrary physical coarse face or prove that a pair-bubble whole-slab face
product has the required isolated-label pattern.

Constructive contract: finite list geometry and exact SU(2) fusion data only;
no `Classical`, choice, `native_decide`, proof hole, noncomputable declaration,
trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
import YMGap.Continuum.Z4FusionPathZeroInsertion

namespace YMGap.Continuum.Z4WholeSlabIsolatedFaceLinkAnnihilation

set_option autoImplicit false
set_option maxRecDepth 20000

open scoped List

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

private theorem nil_sublist_local (A : Type) : ∀ items : List A, [] <+ items
  | [] => List.Sublist.slnil
  | head :: tail => List.Sublist.cons head (nil_sublist_local A tail)

private theorem singleton_sublist_of_mem_local {A : Type} (item : A) :
    ∀ {items : List A}, item ∈ items → [item] <+ items
  | [], hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hmem => by
      rcases List.mem_cons.mp hmem with heq | htail
      · subst head
        exact List.Sublist.cons₂ item (nil_sublist_local A tail)
      · exact List.Sublist.cons head
          (singleton_sublist_of_mem_local item htail)

private theorem natListProduct_eq_zero_of_member_local {A : Type}
    (value : A → Nat) : ∀ (items : List A) {item : A},
    item ∈ items → value item = 0 →
      natListProduct value items = 0
  | [], _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hmem, hzero => by
      rcases List.mem_cons.mp hmem with heq | htail
      · subst head
        simp [natListProduct, hzero]
      · rw [natListProduct,
          natListProduct_eq_zero_of_member_local value tail htail hzero,
          Nat.mul_zero]

/-! ## 1. Local multivalent annihilation -/

/-- A production link whose incident spin word has exactly one nonzero entry
has zero invariant multiplicity.  The selected spin only needs to be bounded
by the production auxiliary cutoff. -/
theorem slabExplicitLinkMultiplicity_eq_zero_of_isolated_nonzero_face
    (K extent : Nat) (physical : Nat → Nat)
    (link : Z4Link) (faceId : Nat)
    (hface : faceId ∈ slabIncidentPlaqIds extent link)
    (hnonzero : physical faceId ≠ 0)
    (hbound : physical faceId ≤ linkAuxiliaryCutoff K)
    (hother : ∀ other,
      other ∈ slabIncidentPlaqIds extent link →
      other ≠ faceId → physical other = 0) :
    slabExplicitLinkMultiplicity K extent physical link = 0 := by
  let incidentIds := slabIncidentPlaqIds extent link
  let spins := incidentIds.map physical
  have hsub : [faceId] <+ incidentIds :=
    singleton_sublist_of_mem_local faceId hface
  have hextension : ZeroExtension [physical faceId] spins := by
    have hraw := ZeroExtension.map_of_sublist physical hsub
      (slabIncidentPlaqIds_nodup extent link)
      (fun other hmem hnotSource =>
        hother other hmem (fun heq =>
          hnotSource (by subst other; simp)))
    simpa only [List.map_singleton] using hraw
  have hincidentLength : spins.length ≤ 6 := by
    unfold spins incidentIds
    simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six extent link
  have hsourceBounded :
      SpinsBounded (linkAuxiliaryCutoff K) [physical faceId] := by
    intro spin hspin
    have heq : spin = physical faceId := List.mem_singleton.mp hspin
    rw [heq]
    exact hbound
  have hextensionMultiplicity :=
    explicitValenceMultiplicity_zeroExtension hextension
      (by simp : [physical faceId].length ≤ 6)
      hincidentLength hsourceBounded
  have hsourceZero :
      explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          [physical faceId].length
          (externalSpinsOfList [physical faceId]) = 0 := by
    change oneValentMultiplicity
      (linkAuxiliaryCutoff K) (physical faceId) = 0
    rw [oneValentMultiplicity_eq_bool_zero]
    simp [boolMultiplicity, hnonzero]
  unfold slabExplicitLinkMultiplicity
  change
    explicitValenceMultiplicity (linkAuxiliaryCutoff K) spins.length
        (externalSpinsOfList spins) = 0
  exact Eq.trans hextensionMultiplicity.symm hsourceZero

/-! ## 2. Propagation into the complete whole-slab link product -/

/-- One isolated nonzero incident face kills the complete product of all
whole-slab production link multiplicities. -/
theorem slabExplicitLinkMultiplicityProduct_eq_zero_of_isolated_nonzero_face
    (K extent : Nat) (physical : Nat → Nat)
    (link : Z4Link) (faceId : Nat)
    (hlink : link ∈ boundaryCompleteSlabLinks extent)
    (hface : faceId ∈ slabIncidentPlaqIds extent link)
    (hnonzero : physical faceId ≠ 0)
    (hbound : physical faceId ≤ linkAuxiliaryCutoff K)
    (hother : ∀ other,
      other ∈ slabIncidentPlaqIds extent link →
      other ≠ faceId → physical other = 0) :
    slabExplicitLinkMultiplicityProduct K extent physical = 0 := by
  unfold slabExplicitLinkMultiplicityProduct
  exact natListProduct_eq_zero_of_member_local
    (slabExplicitLinkMultiplicity K extent physical)
    (boundaryCompleteSlabLinks extent) hlink
    (slabExplicitLinkMultiplicity_eq_zero_of_isolated_nonzero_face
      K extent physical link faceId hface hnonzero hbound hother)

/-- Rational-valued form used by the whole-slab recoupling raw weight. -/
theorem ofNat_slabExplicitLinkMultiplicityProduct_eqv_zero_of_isolated_nonzero_face
    (K extent : Nat) (physical : Nat → Nat)
    (link : Z4Link) (faceId : Nat)
    (hlink : link ∈ boundaryCompleteSlabLinks extent)
    (hface : faceId ∈ slabIncidentPlaqIds extent link)
    (hnonzero : physical faceId ≠ 0)
    (hbound : physical faceId ≤ linkAuxiliaryCutoff K)
    (hother : ∀ other,
      other ∈ slabIncidentPlaqIds extent link →
      other ≠ faceId → physical other = 0) :
    Q'.ofNat
        (slabExplicitLinkMultiplicityProduct K extent physical) ≈ 0 := by
  rw [slabExplicitLinkMultiplicityProduct_eq_zero_of_isolated_nonzero_face
    K extent physical link faceId hlink hface hnonzero hbound hother]
  exact Q'.ofNat_zero_eqv

#print axioms slabExplicitLinkMultiplicity_eq_zero_of_isolated_nonzero_face
#print axioms slabExplicitLinkMultiplicityProduct_eq_zero_of_isolated_nonzero_face
#print axioms ofNat_slabExplicitLinkMultiplicityProduct_eqv_zero_of_isolated_nonzero_face

end YMGap.Continuum.Z4WholeSlabIsolatedFaceLinkAnnihilation
