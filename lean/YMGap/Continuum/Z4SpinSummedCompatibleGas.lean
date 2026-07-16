/-
# The exact arbitrary-cutoff compatible support gas

After summing every spin decoration of a fixed connected face support, the
remaining atoms are exactly the canonical connected supports already used by
the corrected hard-core gas.  Component recombination proves that the
activity of a full support is the product of these connected spin-summed atom
activities.  This module performs the finite reindexing and obtains the actual
arbitrary-cutoff physical partition as the corrected compatible-family gas.
-/

import YMGap.Continuum.Z4SpinSummedSupportComponentLower

namespace YMGap.Continuum.Z4SpinSummedCompatibleGas

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedSupportComponentLower
open YMGap.Continuum.Z4SpinSummedSupportComponentUpper
open YMGap.Continuum.Z4SpinSummedSupportPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Permutation-invariant connected-family activity -/

theorem parametricKSupportFamilyActivity_nonnegative
    (cutoff n : Nat) : ∀ family : List (List Nat),
    (0 : Q') ≤ parametricKSupportFamilyActivity cutoff n family
  | [] => Q'.zero_le_one
  | support :: family =>
      Q'.mul_nonneg _ _
        (parametricKSupportActivity_nonnegative cutoff n support)
        (parametricKSupportFamilyActivity_nonnegative cutoff n family)

theorem parametricKSupportFamilyActivity_perm
    (cutoff n : Nat) :
    ∀ {left right : List (List Nat)}, left.Perm right →
      parametricKSupportFamilyActivity cutoff n left ≈
        parametricKSupportFamilyActivity cutoff n right
  | _, _, List.Perm.nil => Q'.eqv_refl 1
  | _, _, List.Perm.cons _ hperm =>
      Q'.mul_eqv_congr_left _ _ _
        (parametricKSupportFamilyActivity_perm cutoff n hperm)
  | _, _, List.Perm.swap first second rest => by
      change parametricKSupportActivity cutoff n second *
          (parametricKSupportActivity cutoff n first *
            parametricKSupportFamilyActivity cutoff n rest) ≈
        parametricKSupportActivity cutoff n first *
          (parametricKSupportActivity cutoff n second *
            parametricKSupportFamilyActivity cutoff n rest)
      refine Q'.eqv_trans _
        ((parametricKSupportActivity cutoff n second *
            parametricKSupportActivity cutoff n first) *
          parametricKSupportFamilyActivity cutoff n rest) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _
        ((parametricKSupportActivity cutoff n first *
            parametricKSupportActivity cutoff n second) *
          parametricKSupportFamilyActivity cutoff n rest) _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _
  | _, _, List.Perm.trans first second =>
      Q'.eqv_trans _ _ _
        (parametricKSupportFamilyActivity_perm cutoff n first)
        (parametricKSupportFamilyActivity_perm cutoff n second)

theorem parametricKGasFamilyActivity_eqv_ambientOrdered
    (cutoff : Nat) {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalConnectedSurfaceGas n) :
    parametricKSupportFamilyActivity cutoff n family ≈
      parametricKSupportFamilyActivity cutoff n
        (ambientOrderedFamily n family) :=
  parametricKSupportFamilyActivity_perm cutoff n
    (gasFamily_perm_ambientOrdered hfamily)

/-! ## 2. Exact support-to-compatible-family reindexing -/

def parametricKConnectedSupportGasPartition
    (cutoff n : Nat) : Q' :=
  listQSum (parametricKSupportFamilyActivity cutoff n)
    (canonicalConnectedSurfaceGas n)

def parametricKAmbientOrderedSupportGasPartition
    (cutoff n : Nat) : Q' :=
  listQSum (parametricKSupportFamilyActivity cutoff n)
    (ambientOrderedExactGas n)

def parametricKCompatibleSupportGasPartition
    (cutoff n : Nat) : Q' :=
  listQSum (parametricKSupportFamilyActivity cutoff n)
    (canonicalCompatibleAmbientFamilies n)

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

theorem parametricKSupportPartition_eqv_connectedSupportGas
    (cutoff n : Nat) :
    parametricKSupportPartition cutoff n ≈
      parametricKConnectedSupportGasPartition cutoff n := by
  unfold parametricKSupportPartition
    parametricKConnectedSupportGasPartition canonicalConnectedSurfaceGas
  apply listQSum_map_eqv_local
  intro support hsupport
  exact parametricKSupportActivity_eqv_componentFamilyActivity
    cutoff n support hsupport

theorem parametricKConnectedSupportGas_eqv_ambientOrdered
    (cutoff n : Nat) :
    parametricKConnectedSupportGasPartition cutoff n ≈
      parametricKAmbientOrderedSupportGasPartition cutoff n := by
  unfold parametricKConnectedSupportGasPartition
    parametricKAmbientOrderedSupportGasPartition ambientOrderedExactGas
  apply listQSum_map_eqv_local
  intro family hfamily
  exact parametricKGasFamilyActivity_eqv_ambientOrdered cutoff hfamily

theorem parametricKAmbientOrderedSupportGas_eqv_compatible
    (cutoff n : Nat) :
    parametricKAmbientOrderedSupportGasPartition cutoff n ≈
      parametricKCompatibleSupportGasPartition cutoff n := by
  unfold parametricKAmbientOrderedSupportGasPartition
    parametricKCompatibleSupportGasPartition
  exact listQSum_perm (parametricKSupportFamilyActivity cutoff n)
    (ambientOrderedExactGas_perm_compatibleFamilies n)

theorem parametricKSupportPartition_eqv_compatibleSupportGas
    (cutoff n : Nat) :
    parametricKSupportPartition cutoff n ≈
      parametricKCompatibleSupportGasPartition cutoff n :=
  Q'.eqv_trans _ _ _
    (parametricKSupportPartition_eqv_connectedSupportGas cutoff n)
    (Q'.eqv_trans _ _ _
      (parametricKConnectedSupportGas_eqv_ambientOrdered cutoff n)
      (parametricKAmbientOrderedSupportGas_eqv_compatible cutoff n))

theorem parametricKPhysicalPartition_eqv_compatibleSupportGas
    (cutoff n : Nat) :
    parametricKPhysicalPartition anchorCoupling cutoff n ≈
      parametricKCompatibleSupportGasPartition cutoff n :=
  Q'.eqv_trans _ _ _
    (parametricKPhysicalPartition_eqv_supportPartition cutoff n)
    (parametricKSupportPartition_eqv_compatibleSupportGas cutoff n)

/-! ## 3. Exact finite compatible-gas probabilities -/

def parametricKCompatibleSupportEventNumerator
    (cutoff n : Nat) (event : List (List Nat) → Bool) : Q' :=
  listQSum (parametricKSupportFamilyActivity cutoff n)
    ((canonicalCompatibleAmbientFamilies n).filter event)

theorem parametricKCompatibleSupportGasPartition_nonnegative
    (cutoff n : Nat) :
    (0 : Q') ≤ parametricKCompatibleSupportGasPartition cutoff n := by
  unfold parametricKCompatibleSupportGasPartition
  exact listQSum_nonnegative _
    (parametricKSupportFamilyActivity_nonnegative cutoff n) _

theorem parametricKCompatibleSupportGasPartition_one_le
    (cutoff n : Nat) :
    (1 : Q') ≤ parametricKCompatibleSupportGasPartition cutoff n :=
  Q'.le_trans' _ _ _
    (parametricKSupportPartition_one_le cutoff n)
    (Q'.le_of_eqv
      (parametricKSupportPartition_eqv_compatibleSupportGas cutoff n))

theorem parametricKCompatibleSupportGasPartition_pos
    (cutoff n : Nat) :
    (0 : Q') < parametricKCompatibleSupportGasPartition cutoff n :=
  YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
    (by decide)
    (parametricKCompatibleSupportGasPartition_one_le cutoff n)

theorem parametricKCompatibleSupportEventNumerator_nonnegative
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    (0 : Q') ≤
      parametricKCompatibleSupportEventNumerator cutoff n event := by
  unfold parametricKCompatibleSupportEventNumerator
  exact listQSum_nonnegative _
    (parametricKSupportFamilyActivity_nonnegative cutoff n) _

theorem parametricKCompatibleSupportEventNumerator_le_partition
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    parametricKCompatibleSupportEventNumerator cutoff n event ≤
      parametricKCompatibleSupportGasPartition cutoff n := by
  unfold parametricKCompatibleSupportEventNumerator
    parametricKCompatibleSupportGasPartition
  exact listQSum_filter_le _ event
    (parametricKSupportFamilyActivity_nonnegative cutoff n) _

def parametricKCompatibleSupportEventProbability
    (cutoff n : Nat) (event : List (List Nat) → Bool) : Q' :=
  Q'.divPos (parametricKCompatibleSupportEventNumerator cutoff n event)
    (parametricKCompatibleSupportGasPartition cutoff n)
    (parametricKCompatibleSupportGasPartition_pos cutoff n)

theorem parametricKCompatibleSupportEventProbability_nonnegative
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    (0 : Q') ≤
      parametricKCompatibleSupportEventProbability cutoff n event := by
  unfold parametricKCompatibleSupportEventProbability Q'.divPos
  exact Q'.mul_nonneg _ _
    (parametricKCompatibleSupportEventNumerator_nonnegative
      cutoff n event)
    (Q'.le_of_lt
      (Q'.recipPos_pos
        (parametricKCompatibleSupportGasPartition cutoff n)
        (parametricKCompatibleSupportGasPartition_pos cutoff n)))

theorem parametricKCompatibleSupportEventProbability_le_one
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    parametricKCompatibleSupportEventProbability cutoff n event ≤
      (1 : Q') := by
  unfold parametricKCompatibleSupportEventProbability
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _
    (parametricKCompatibleSupportEventNumerator_le_partition
      cutoff n event)
    (Q'.ge_of_eqv
      (Q'.one_mul_eqv
        (parametricKCompatibleSupportGasPartition cutoff n)))

end YMGap.Continuum.Z4SpinSummedCompatibleGas

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinSummedCompatibleGas.parametricKSupportFamilyActivity_perm
#print axioms YMGap.Continuum.Z4SpinSummedCompatibleGas.parametricKSupportPartition_eqv_compatibleSupportGas
#print axioms YMGap.Continuum.Z4SpinSummedCompatibleGas.parametricKPhysicalPartition_eqv_compatibleSupportGas
#print axioms YMGap.Continuum.Z4SpinSummedCompatibleGas.parametricKCompatibleSupportGasPartition_pos
#print axioms YMGap.Continuum.Z4SpinSummedCompatibleGas.parametricKCompatibleSupportEventProbability_le_one
