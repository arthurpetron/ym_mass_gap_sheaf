/-
# Permutation-invariant residual bound for an equal physical pair

The ordered channel bounds of `Z4EqualPairResidualMultiplicityBound` are
lifted here to the literal valence-zero-through-six production formula.  An
actual incident-spin list may place the two equal source labels anywhere;
the existing constructive physical permutation theorem moves them to the
front, after which only the sum of the remaining at-most-four labels is
charged.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.Z4EqualPairResidualMultiplicityBound
import YMGap.Continuum.Z4FusionMultiplicityPermutationLift

namespace YMGap.Continuum.Z4EqualPairResidualValenceBound

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option autoImplicit false

open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.Z4EqualPairResidualMultiplicityBound
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4SpinDependentLocalMultiplicityBound
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

private theorem boolMultiplicity_le_one (allowed : Bool) :
    boolMultiplicity allowed <= 1 := by
  cases allowed <;> decide

private theorem one_le_spinSumCube (sum : Nat) :
    1 <= spinSumCube sum := by
  unfold spinSumCube
  exact Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt (Nat.mul_pos (by omega)
      (Nat.mul_pos (by omega) (by omega))))

/-! ## 1. Canonical equal-pair valences -/

/-- For an equal pair followed by at most four labels, the complete explicit
valence formula is bounded by the residual-label cubic envelope. -/
theorem explicitValenceMultiplicity_equalPair_le_residualSpinSumCube
    (cutoff spin : Nat) (rest : List Nat)
    (hrest : rest.length <= 4) :
    explicitValenceMultiplicity cutoff (spin :: spin :: rest).length
        (externalSpinsOfList (spin :: spin :: rest)) <=
      spinSumCube (natListSum rest) := by
  cases rest with
  | nil =>
      change twoValentMultiplicity cutoff spin spin <= spinSumCube 0
      rw [twoValentMultiplicity_eq_bool_zero_output]
      exact Nat.le_trans (boolMultiplicity_le_one _)
        (one_le_spinSumCube 0)
  | cons a rest =>
      cases rest with
      | nil =>
          change boolMultiplicity (fusionOK spin spin a) <= spinSumCube a
          exact Nat.le_trans (boolMultiplicity_le_one _)
            (one_le_spinSumCube a)
      | cons b rest =>
          cases rest with
          | nil =>
              simpa [externalSpinsOfList, natListSum] using
                oneChannelMultiplicity_equalPair_le_residualSpinSumCube
                  cutoff spin a b
          | cons c rest =>
              cases rest with
              | nil =>
                  change twoChannelMultiplicity cutoff spin spin a b c <=
                    spinSumCube (a + (b + c))
                  rw [show a + (b + c) = a + b + c by omega]
                  exact
                    twoChannelMultiplicity_equalPair_le_residualSpinSumCube
                      cutoff spin a b c
              | cons d rest =>
                  cases rest with
                  | nil =>
                      change
                        threeChannelMultiplicity cutoff spin spin a b c d <=
                          spinSumCube (a + (b + (c + d)))
                      rw [show a + (b + (c + d)) = a + b + c + d by omega]
                      exact
                        threeChannelMultiplicity_equalPair_le_residualSpinSumCube
                          cutoff spin a b c d
                  | cons e rest =>
                      simp only [List.length_cons] at hrest
                      omega

/-! ## 2. Actual physical order -/

/-- The production multiplicity of any physical incident list containing a
permuted equal pair is bounded only by the residual labels. -/
theorem explicitValenceMultiplicity_physical_equalPair_le_residualSpinSumCube
    {K spin : Nat} {actual rest : List Nat}
    (hperm : actual.Perm (spin :: spin :: rest))
    (hlength : actual.length <= 6)
    (hbounded : SpinsBounded K actual) :
    explicitValenceMultiplicity (linkAuxiliaryCutoff K) actual.length
        (externalSpinsOfList actual) <=
      spinSumCube (natListSum rest) := by
  have hrest : rest.length <= 4 := by
    have hsize := hperm.length_eq
    simp only [List.length_cons] at hsize
    omega
  rw [explicitValenceMultiplicity_physical_perm
    hperm hlength hbounded]
  exact explicitValenceMultiplicity_equalPair_le_residualSpinSumCube
    (linkAuxiliaryCutoff K) spin rest hrest

end YMGap.Continuum.Z4EqualPairResidualValenceBound

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4EqualPairResidualValenceBound.explicitValenceMultiplicity_equalPair_le_residualSpinSumCube
#print axioms YMGap.Continuum.Z4EqualPairResidualValenceBound.explicitValenceMultiplicity_physical_equalPair_le_residualSpinSumCube
