/-
# Reordering the two BF4 inward-mate faces at a physical link

The local inward-mate fusion theorem is stated with the two changed cube-face
labels at the head of the incident spin list.  A physical link presents its
incident plaquettes in a geometric order.  This file proves the exact compiler
between those presentations: if the source incident word and the mate incident
word carry the corresponding permutation witnesses, then the production link
multiplicity obeys the same one-stretched-continuation bound.

The remaining global obligation is therefore geometric and strand-theoretic:
construct these permutation witnesses at each boundary link and reroute the
resulting stretched continuations componentwise.  This file does not assert
that global rerouting, a transition floor, a Poincare inequality, a spectral
gap, or a continuum result.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or trusted external computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionSupport
import YMGap.Continuum.Z4FusionMultiplicityPermutationLift

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionReordering

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionSupport
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4FusionPathZeroInsertion

/-- The even inward mate stays inside every positive physical cutoff. -/
theorem evenInwardMateLabel_le_cutoff
    {K spin : Nat} (hK : 1 ≤ K) (hspin : spin ≤ K) :
    evenInwardMateLabel spin ≤ K := by
  unfold evenInwardMateLabel
  by_cases hzero : spin = 0
  · rw [if_pos hzero]
    exact hK
  · rw [if_neg hzero]
    omega

/-- **Physical-link reordering compiler.**  The two changed cube faces may
occur anywhere in the canonical incident-spin word.  Once explicit source and
mate permutation witnesses move them to the first two slots, the already
proved local SU(2) inequality transports back verbatim.  The sole additive
term is the stretched-channel continuation in the chosen front presentation. -/
theorem explicitValenceMultiplicity_physical_inwardMate_of_permutations
    (K left right : Nat) (rest source mate : List Nat)
    (hK : 1 ≤ K)
    (hlength : (left :: right :: rest).length ≤ 6)
    (hbounded : SpinsBounded K (left :: right :: rest))
    (hsource : source.Perm (left :: right :: rest))
    (hmate : mate.Perm
      (evenInwardMateLabel left ::
        evenInwardMateLabel right :: rest)) :
    explicitValenceMultiplicity (linkAuxiliaryCutoff K)
        source.length (externalSpinsOfList source) ≤
      explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          mate.length (externalSpinsOfList mate) +
        explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          ((left + right) :: rest).length
          (externalSpinsOfList ((left + right) :: rest)) := by
  have hsourceLength : source.length ≤ 6 := by
    rw [hsource.length_eq]
    exact hlength
  have hsourceBounded : SpinsBounded K source :=
    spinsBounded_of_perm hsource.symm hbounded
  have hleftK : left ≤ K := hbounded left (by simp)
  have hrightK : right ≤ K := hbounded right (by simp)
  have hrestK : SpinsBounded K rest := by
    intro spin hspin
    exact hbounded spin (by simp [hspin])
  have hmateFrontBounded : SpinsBounded K
      (evenInwardMateLabel left ::
        evenInwardMateLabel right :: rest) := by
    intro spin hspin
    rcases List.mem_cons.mp hspin with hspin | hspin
    · subst spin
      exact evenInwardMateLabel_le_cutoff hK hleftK
    · rcases List.mem_cons.mp hspin with hspin | hspin
      · subst spin
        exact evenInwardMateLabel_le_cutoff hK hrightK
      · exact hrestK spin hspin
  have hmateLength : mate.length ≤ 6 := by
    rw [hmate.length_eq]
    simpa only [List.length_cons] using hlength
  have hmateBounded : SpinsBounded K mate :=
    spinsBounded_of_perm hmate.symm hmateFrontBounded
  have hsourceEq := explicitValenceMultiplicity_physical_perm
    hsource hsourceLength hsourceBounded
  have hmateEq := explicitValenceMultiplicity_physical_perm
    hmate hmateLength hmateBounded
  calc
    explicitValenceMultiplicity (linkAuxiliaryCutoff K)
        source.length (externalSpinsOfList source) =
        explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          (left :: right :: rest).length
          (externalSpinsOfList (left :: right :: rest)) := hsourceEq
    _ ≤ explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          (evenInwardMateLabel left ::
            evenInwardMateLabel right :: rest).length
          (externalSpinsOfList
            (evenInwardMateLabel left ::
              evenInwardMateLabel right :: rest)) +
        explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          ((left + right) :: rest).length
          (externalSpinsOfList ((left + right) :: rest)) :=
      explicitValenceMultiplicity_physical_inwardMate_le_add_stretched
        K left right rest hK hlength hbounded
    _ = explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          mate.length (externalSpinsOfList mate) +
        explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          ((left + right) :: rest).length
          (externalSpinsOfList ((left + right) :: rest)) := by
      rw [← hmateEq]

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionReordering

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionReordering.evenInwardMateLabel_le_cutoff
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionReordering.explicitValenceMultiplicity_physical_inwardMate_of_permutations
