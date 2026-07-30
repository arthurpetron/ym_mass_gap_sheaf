/-
# Singlet-channel injection for a pair of fundamental SU(2) spins

Two twice-spin-one external labels admit the vacuum channel.  In the
finite left-fusion resolver, retaining that one channel gives a constructive
injection from every old vacuum-ending fusion path into the resolver with
the pair `1, 1` prepended.

This is the local algebra needed to compare the BF4 vacuum row with the
closed lower-cube row.  No averaging, division, or choice is used: the proof
is the order bound for one named summand of a finite natural-number sum.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.Z4FusionMultiplicityPermutationLift

namespace YMGap.Continuum.Z4FusionPairSingletInjection

open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. A named summand is bounded by the finite natural sum -/

theorem natListSum_map_term_le
    {A : Type} (term : A → Nat) :
    ∀ {chosen : A} {xs : List A}, chosen ∈ xs →
      term chosen ≤ natListSum (xs.map term)
  | _, [], hmem => by simp at hmem
  | chosen, head :: tail, hmem => by
      simp only [List.mem_cons] at hmem
      simp only [List.map_cons, natListSum]
      rcases hmem with rfl | htail
      · exact Nat.le_add_right _ _
      · exact Nat.le_trans
          (natListSum_map_term_le term htail)
          (Nat.le_add_left _ _)

/-! ## 2. The fundamental pair contains the old resolver -/

/-- Prepending two fundamental twice-spin labels cannot decrease the number
of vacuum-ending fusion paths.  The injection selects the `channel = 0`
summand of `1 ⊗ 1`; zero insertion then identifies its continuation with the
old path count. -/
theorem fusionPathMultiplicity_le_pair_one
    {cutoff : Nat} (spins : List Nat)
    (hspins : SpinsBounded cutoff spins) :
    fusionPathMultiplicity cutoff spins ≤
      fusionPathMultiplicity cutoff (1 :: 1 :: spins) := by
  rw [fusionPathMultiplicity_cons_cons]
  let term := fun channel =>
    if fusionOK 1 1 channel then
      fusionPathMultiplicity cutoff (channel :: spins)
    else 0
  have hzeroMem : 0 ∈ List.range (cutoff + 1) := by
    exact List.mem_range.mpr (Nat.zero_lt_succ cutoff)
  have hterm :=
    natListSum_map_term_le term hzeroMem
  have hsinglet :
      term 0 = fusionPathMultiplicity cutoff spins := by
    unfold term
    rw [fusionOK_zero_output_eq_decide]
    simp only [decide_true, if_true]
    exact fusionPathMultiplicity_zero_cons spins hspins
  rw [hsinglet] at hterm
  exact hterm

/-- Production-cutoff specialization: a pair of fundamental labels can be
inserted in front of any cutoff-`K` physical spin list. -/
theorem fusionPathMultiplicity_physical_le_pair_one
    {K : Nat} (spins : List Nat)
    (hspins : SpinsBounded K spins) :
    fusionPathMultiplicity (linkAuxiliaryCutoff K) spins ≤
      fusionPathMultiplicity (linkAuxiliaryCutoff K)
        (1 :: 1 :: spins) := by
  apply fusionPathMultiplicity_le_pair_one
  intro spin hspin
  exact Nat.le_trans (hspins spin hspin)
    (externalCutoff_le_linkAuxiliaryCutoff K)

/-! ## 3. Pair replacement inside a physical valence-six list -/

/-- If one physical incident-spin list is a permutation of `0,0,rest` and
another is a permutation of `1,1,rest`, then the production explicit
valence multiplicity of the first is bounded by that of the second. -/
theorem explicitValenceMultiplicity_physical_pair_replacement_le
    {K : Nat} {oldSpins newSpins rest : List Nat}
    (holdPerm : oldSpins.Perm (0 :: 0 :: rest))
    (hnewPerm : newSpins.Perm (1 :: 1 :: rest))
    (hlength : oldSpins.length ≤ 6)
    (holdBounded : SpinsBounded K oldSpins)
    (hnewBounded : SpinsBounded K newSpins) :
    explicitValenceMultiplicity
        (linkAuxiliaryCutoff K) oldSpins.length
        (externalSpinsOfList oldSpins) ≤
      explicitValenceMultiplicity
        (linkAuxiliaryCutoff K) newSpins.length
        (externalSpinsOfList newSpins) := by
  have hnewLength : newSpins.length ≤ 6 := by
    have holdLengthEq := holdPerm.length_eq
    have hnewLengthEq := hnewPerm.length_eq
    simp only [List.length_cons] at holdLengthEq hnewLengthEq
    omega
  have holdAux : SpinsBounded
      (linkAuxiliaryCutoff K) oldSpins := by
    intro spin hspin
    exact Nat.le_trans (holdBounded spin hspin)
      (externalCutoff_le_linkAuxiliaryCutoff K)
  have hnewAux : SpinsBounded
      (linkAuxiliaryCutoff K) newSpins := by
    intro spin hspin
    exact Nat.le_trans (hnewBounded spin hspin)
      (externalCutoff_le_linkAuxiliaryCutoff K)
  have hcanonicalBounded :
      SpinsBounded K (0 :: 0 :: rest) :=
    spinsBounded_of_perm holdPerm holdBounded
  have hrestBounded : SpinsBounded K rest := by
    intro spin hspin
    exact hcanonicalBounded spin (by simp [hspin])
  have hrestAux : SpinsBounded
      (linkAuxiliaryCutoff K) rest := by
    intro spin hspin
    exact Nat.le_trans (hrestBounded spin hspin)
      (externalCutoff_le_linkAuxiliaryCutoff K)
  have hzeroRestAux : SpinsBounded
      (linkAuxiliaryCutoff K) (0 :: rest) := by
    intro spin hspin
    rcases List.mem_cons.mp hspin with rfl | hspin
    · exact Nat.zero_le _
    · exact hrestAux spin hspin
  rw [← fusionPathMultiplicity_eq_explicit_of_length_le_six
      oldSpins hlength holdAux,
    ← fusionPathMultiplicity_eq_explicit_of_length_le_six
      newSpins hnewLength hnewAux]
  calc
    fusionPathMultiplicity (linkAuxiliaryCutoff K) oldSpins =
        fusionPathMultiplicity (linkAuxiliaryCutoff K)
          (0 :: 0 :: rest) :=
      fusionPathMultiplicity_physical_perm
        holdPerm hlength holdBounded
    _ = fusionPathMultiplicity (linkAuxiliaryCutoff K)
          (0 :: rest) :=
      fusionPathMultiplicity_zero_cons
        (0 :: rest) hzeroRestAux
    _ = fusionPathMultiplicity (linkAuxiliaryCutoff K) rest :=
      fusionPathMultiplicity_zero_cons rest hrestAux
    _ ≤ fusionPathMultiplicity (linkAuxiliaryCutoff K)
          (1 :: 1 :: rest) :=
      fusionPathMultiplicity_physical_le_pair_one rest hrestBounded
    _ = fusionPathMultiplicity (linkAuxiliaryCutoff K) newSpins :=
      (fusionPathMultiplicity_physical_perm
        hnewPerm hnewLength hnewBounded).symm

end YMGap.Continuum.Z4FusionPairSingletInjection

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4FusionPairSingletInjection.natListSum_map_term_le
#print axioms YMGap.Continuum.Z4FusionPairSingletInjection.fusionPathMultiplicity_le_pair_one
#print axioms YMGap.Continuum.Z4FusionPairSingletInjection.fusionPathMultiplicity_physical_le_pair_one
#print axioms YMGap.Continuum.Z4FusionPairSingletInjection.explicitValenceMultiplicity_physical_pair_replacement_le
