/-
# Singlet-channel injection for an arbitrary equal pair of SU(2) spins

For every twice-spin label `spin`, the tensor product `spin tensor spin`
contains the vacuum channel.  Selecting that named channel gives a
constructive injection from every old vacuum-ending fusion path into the
resolver with `spin, spin` prepended.

This all-spin form is the local algebra needed to connect the vacuum to the
closed lower cube carrying any label admitted by the production cutoff.  It
does not assert a cutoff-uniform probability or spectral estimate.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.Z4FusionPairSingletInjection

namespace YMGap.Continuum.Z4FusionEqualPairSingletInjection

open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4FusionPairSingletInjection
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. An arbitrary equal pair contains the old resolver -/

/-- Prepending two equal twice-spin labels cannot decrease the number of
vacuum-ending fusion paths.  The injection selects the `channel = 0`
summand of `spin tensor spin`. -/
theorem fusionPathMultiplicity_le_equal_pair
    {cutoff spin : Nat} (spins : List Nat)
    (hspins : SpinsBounded cutoff spins) :
    fusionPathMultiplicity cutoff spins <=
      fusionPathMultiplicity cutoff (spin :: spin :: spins) := by
  rw [fusionPathMultiplicity_cons_cons]
  let term := fun channel =>
    if fusionOK spin spin channel then
      fusionPathMultiplicity cutoff (channel :: spins)
    else 0
  have hzeroMem : 0 ∈ List.range (cutoff + 1) := by
    exact List.mem_range.mpr (Nat.zero_lt_succ cutoff)
  have hterm := natListSum_map_term_le term hzeroMem
  have hsinglet :
      term 0 = fusionPathMultiplicity cutoff spins := by
    unfold term
    rw [fusionOK_zero_output_eq_decide]
    simp only [decide_true, if_true]
    exact fusionPathMultiplicity_zero_cons spins hspins
  rw [hsinglet] at hterm
  exact hterm

/-- Production-cutoff specialization for an arbitrary equal pair. -/
theorem fusionPathMultiplicity_physical_le_equal_pair
    {K spin : Nat} (spins : List Nat)
    (hspins : SpinsBounded K spins) :
    fusionPathMultiplicity (linkAuxiliaryCutoff K) spins <=
      fusionPathMultiplicity (linkAuxiliaryCutoff K)
        (spin :: spin :: spins) := by
  apply fusionPathMultiplicity_le_equal_pair
  intro value hvalue
  exact Nat.le_trans (hspins value hvalue)
    (externalCutoff_le_linkAuxiliaryCutoff K)

/-! ## 2. Equal-pair replacement inside a physical valence-six list -/

/-- If one physical incident-spin list is a permutation of `0,0,rest` and
another is a permutation of `spin,spin,rest`, then replacing the vacuum pair
by the equal pair cannot decrease the production multiplicity. -/
theorem explicitValenceMultiplicity_physical_equal_pair_replacement_le
    {K spin : Nat} {oldSpins newSpins rest : List Nat}
    (holdPerm : oldSpins.Perm (0 :: 0 :: rest))
    (hnewPerm : newSpins.Perm (spin :: spin :: rest))
    (hlength : oldSpins.length <= 6)
    (holdBounded : SpinsBounded K oldSpins)
    (hnewBounded : SpinsBounded K newSpins) :
    explicitValenceMultiplicity
        (linkAuxiliaryCutoff K) oldSpins.length
        (externalSpinsOfList oldSpins) <=
      explicitValenceMultiplicity
        (linkAuxiliaryCutoff K) newSpins.length
        (externalSpinsOfList newSpins) := by
  have hnewLength : newSpins.length <= 6 := by
    have holdLengthEq := holdPerm.length_eq
    have hnewLengthEq := hnewPerm.length_eq
    simp only [List.length_cons] at holdLengthEq hnewLengthEq
    omega
  have holdAux : SpinsBounded
      (linkAuxiliaryCutoff K) oldSpins := by
    intro value hvalue
    exact Nat.le_trans (holdBounded value hvalue)
      (externalCutoff_le_linkAuxiliaryCutoff K)
  have hnewAux : SpinsBounded
      (linkAuxiliaryCutoff K) newSpins := by
    intro value hvalue
    exact Nat.le_trans (hnewBounded value hvalue)
      (externalCutoff_le_linkAuxiliaryCutoff K)
  have hcanonicalBounded :
      SpinsBounded K (0 :: 0 :: rest) :=
    spinsBounded_of_perm holdPerm holdBounded
  have hrestBounded : SpinsBounded K rest := by
    intro value hvalue
    exact hcanonicalBounded value (by simp [hvalue])
  have hrestAux : SpinsBounded
      (linkAuxiliaryCutoff K) rest := by
    intro value hvalue
    exact Nat.le_trans (hrestBounded value hvalue)
      (externalCutoff_le_linkAuxiliaryCutoff K)
  have hzeroRestAux : SpinsBounded
      (linkAuxiliaryCutoff K) (0 :: rest) := by
    intro value hvalue
    rcases List.mem_cons.mp hvalue with rfl | hvalue
    · exact Nat.zero_le _
    · exact hrestAux value hvalue
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
    _ <= fusionPathMultiplicity (linkAuxiliaryCutoff K)
          (spin :: spin :: rest) :=
      fusionPathMultiplicity_physical_le_equal_pair
        rest hrestBounded
    _ = fusionPathMultiplicity (linkAuxiliaryCutoff K) newSpins :=
      (fusionPathMultiplicity_physical_perm
        hnewPerm hnewLength hnewBounded).symm

end YMGap.Continuum.Z4FusionEqualPairSingletInjection

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4FusionEqualPairSingletInjection.fusionPathMultiplicity_le_equal_pair
#print axioms YMGap.Continuum.Z4FusionEqualPairSingletInjection.fusionPathMultiplicity_physical_le_equal_pair
#print axioms YMGap.Continuum.Z4FusionEqualPairSingletInjection.explicitValenceMultiplicity_physical_equal_pair_replacement_le
