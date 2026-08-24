/-
# List-coordinate form of the residual fusion bound

This small transport module identifies the prefix-coordinate sum used by the
generic local multiplicity theorem with the ordinary sum of the corresponding
finite spin list.  The result makes both the generic and equal-pair bounds
permutation-friendly and gives them one common residual-list language.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.Z4EqualPairResidualValenceBound

namespace YMGap.Continuum.Z4ResidualListMultiplicityBound

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option autoImplicit false

open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4SpinDependentLocalMultiplicityBound
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Prefix coordinates are an ordinary list sum -/

theorem externalPrefixSpinSum_eq_rangeSum
    (degree : Nat) (external : Nat -> Nat) :
    externalPrefixSpinSum degree external =
      natListSum ((List.range degree).map external) := by
  induction degree with
  | zero => rfl
  | succ degree ih =>
      change externalPrefixSpinSum degree external + external degree = _
      rw [List.range_succ, List.map_append, natListSum_append, ih]
      simp [natListSum]

/-- `externalSpinsOfList` only reindexes a finite word. -/
theorem externalPrefixSpinSum_externalSpinsOfList
    (spins : List Nat) :
    externalPrefixSpinSum spins.length (externalSpinsOfList spins) =
      natListSum spins := by
  rw [externalPrefixSpinSum_eq_rangeSum]
  induction spins with
  | nil => rfl
  | cons head tail ih =>
      change
        natListSum
            ((List.range (tail.length + 1)).map
              (externalSpinsOfList (head :: tail))) =
          natListSum (head :: tail)
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, natListSum, List.map_map]
      change head +
          natListSum
            ((List.range tail.length).map (externalSpinsOfList tail)) =
        head + natListSum tail
      exact congrArg (fun value => head + value) ih

theorem natListSum_perm {left right : List Nat}
    (hperm : left.Perm right) :
    natListSum left = natListSum right := by
  induction hperm with
  | nil => rfl
  | cons head hperm ih =>
      simp only [natListSum]
      rw [ih]
  | swap first second tail =>
      simp only [natListSum]
      omega
  | trans _ _ ihLeft ihRight =>
      exact Eq.trans ihLeft ihRight

/-! ## 2. Generic physical valences in residual-list form -/

/-- Every explicit valence through degree six is bounded by the cubic of the
ordinary sum of its incident-spin list. -/
theorem explicitValenceMultiplicity_list_le_spinSumCube
    (cutoff : Nat) (spins : List Nat)
    (hlength : spins.length <= 6) :
    explicitValenceMultiplicity cutoff spins.length
        (externalSpinsOfList spins) <=
      spinSumCube (natListSum spins) := by
  have hbound := explicitValenceMultiplicity_le_spinSumCube
    (cutoff := cutoff) (degree := spins.length)
    (externalSpinsOfList spins) hlength
  rw [externalPrefixSpinSum_externalSpinsOfList] at hbound
  exact hbound

/-- Reindexing an actual physical incident list by a permutation preserves
the residual-list upper bound. -/
theorem explicitValenceMultiplicity_physical_perm_le_spinSumCube
    {K : Nat} {actual residual : List Nat}
    (hperm : actual.Perm residual)
    (hlength : actual.length <= 6)
    (hbounded : SpinsBounded K actual) :
    explicitValenceMultiplicity (linkAuxiliaryCutoff K) actual.length
        (externalSpinsOfList actual) <=
      spinSumCube (natListSum residual) := by
  rw [YMGap.Continuum.Z4FusionMultiplicityPermutationLift.explicitValenceMultiplicity_physical_perm
    hperm hlength hbounded]
  have hresidualLength : residual.length <= 6 := by
    rw [<- hperm.length_eq]
    exact hlength
  exact explicitValenceMultiplicity_list_le_spinSumCube
    (linkAuxiliaryCutoff K) residual hresidualLength

end YMGap.Continuum.Z4ResidualListMultiplicityBound

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4ResidualListMultiplicityBound.externalPrefixSpinSum_externalSpinsOfList
#print axioms YMGap.Continuum.Z4ResidualListMultiplicityBound.natListSum_perm
#print axioms YMGap.Continuum.Z4ResidualListMultiplicityBound.explicitValenceMultiplicity_list_le_spinSumCube
#print axioms YMGap.Continuum.Z4ResidualListMultiplicityBound.explicitValenceMultiplicity_physical_perm_le_spinSumCube
