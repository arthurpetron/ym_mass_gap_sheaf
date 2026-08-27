/-
# Coupling-parametric cutoff-uniform tail for the canonical face cylinder

Below the derived strong-coupling anchor, every fixed-support spin sum is
bounded termwise by its anchor value.  Therefore the cutoff-uniform pinned
tail proved at the anchor also controls the exact compatible-support law at
every explicitly named coupling in that interval.

The result is stated directly for the normalized coupling-parametric law used
by the centered thermodynamic sequence.  No identification between opaque
constants or specialized probability definitions is required.
-/

import YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
import YMGap.Continuum.Z4SpinSummedCanonicalFaceEventPinnedTail

namespace YMGap.Continuum.Z4CouplingParametricCanonicalFaceEventPinnedTail

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilityMarkedBound
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalFaceEventPinnedTail
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4SpinSummedCanonicalFaceEventPinnedTail
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedSupportComponentUpper
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Monotone comparison with the anchor activity -/

def couplingParametricKCanonicalPinnedLargeActivity
    (coupling : Q') (cutoff n face sizeFloor : Nat) : Q' :=
  markedActivitySum
    (couplingParametricKSupportActivity coupling cutoff n)
    (canonicalPinnedLargeMark face sizeFloor)
    (canonicalSurfacePolymers n)

theorem couplingParametricKCanonicalPinnedLargeActivity_le_anchor
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (cutoff n face sizeFloor : Nat) :
    couplingParametricKCanonicalPinnedLargeActivity
        coupling cutoff n face sizeFloor ≤
      parametricKCanonicalPinnedLargeActivity
        cutoff n face sizeFloor := by
  unfold couplingParametricKCanonicalPinnedLargeActivity
    parametricKCanonicalPinnedLargeActivity markedActivitySum
  apply listQSum_le_of_injective
    ((canonicalSurfacePolymers n).filter
      (canonicalPinnedLargeMark face sizeFloor))
    ((canonicalSurfacePolymers n).filter
      (canonicalPinnedLargeMark face sizeFloor))
    (couplingParametricKSupportActivity coupling cutoff n)
    (parametricKSupportActivity cutoff n)
    (fun polymer => polymer)
  · exact List.filter_sublist.nodup (canonicalSurfacePolymers_nodup n)
  · intro polymer hpolymer
    exact hpolymer
  · intro left _ right _ heq
    exact heq
  · intro polymer hpolymer
    exact couplingParametricKSupportActivity_le_anchor
      hcoupling hle cutoff n polymer
  · intro polymer _
    exact parametricKSupportActivity_nonnegative cutoff n polymer

theorem couplingParametricKCanonicalPinnedLargeActivity_le_tail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (cutoff n face sizeFloor : Nat) :
    couplingParametricKCanonicalPinnedLargeActivity
        coupling cutoff n face sizeFloor ≤
      Q'.ofNat 2 * anchorDecoratedEffectiveRatio ^ sizeFloor := by
  exact Q'.le_trans' _ _ _
    (couplingParametricKCanonicalPinnedLargeActivity_le_anchor
      hcoupling hle cutoff n face sizeFloor)
    (parametricKCanonicalPinnedLargeActivity_le_tail
      cutoff n face sizeFloor)

/-! ## 2. Exact generic-gas identification -/

private theorem familyWeight_eq_couplingParametricKSupportFamilyActivity
    (coupling : Q') (cutoff n : Nat) : ∀ family : List (List Nat),
    familyWeight
        (couplingParametricKSupportActivity coupling cutoff n) family =
      couplingParametricKSupportFamilyActivity
        coupling cutoff n family
  | [] => rfl
  | support :: family => by
      change couplingParametricKSupportActivity coupling cutoff n support *
          familyWeight
            (couplingParametricKSupportActivity coupling cutoff n) family =
        couplingParametricKSupportActivity coupling cutoff n support *
          couplingParametricKSupportFamilyActivity
            coupling cutoff n family
      rw [familyWeight_eq_couplingParametricKSupportFamilyActivity
        coupling cutoff n family]

private theorem genericCouplingParametricKPartition_eqv
    (coupling : Q') (cutoff n : Nat) :
    partition (canonicalPolymerCompatibleB n)
        (couplingParametricKSupportActivity coupling cutoff n)
        (canonicalSurfacePolymers n) ≈
      couplingParametricKCompatibleSupportGasPartition
        coupling cutoff n := by
  unfold partition couplingParametricKCompatibleSupportGasPartition
  rw [genericCompatibleFamilies_eq_canonical]
  exact listQSum_congr
    (fun family => Q'.eqv_of_eq
      (familyWeight_eq_couplingParametricKSupportFamilyActivity
        coupling cutoff n family)) _

private theorem genericCouplingParametricKEventNumerator_eqv
    (coupling : Q') (cutoff n : Nat)
    (event : List (List Nat) → Bool) :
    eventNumerator (canonicalPolymerCompatibleB n)
        (couplingParametricKSupportActivity coupling cutoff n)
        (canonicalSurfacePolymers n) event ≈
      couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff n event := by
  unfold eventNumerator
    couplingParametricKCompatibleSupportEventNumerator
  rw [genericCompatibleFamilies_eq_canonical]
  exact listQSum_congr
    (fun family => Q'.eqv_of_eq
      (familyWeight_eq_couplingParametricKSupportFamilyActivity
        coupling cutoff n family)) _

/-! ## 3. The normalized probability tail in the thermodynamic law -/

theorem couplingParametricKCompatibleSupportEventProbability_mono
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (first second : List (List Nat) → Bool)
    (himp : ∀ family,
      family ∈ canonicalCompatibleAmbientFamilies n →
      first family = true → second family = true) :
    couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff n first ≤
      couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff n second := by
  have hnumerator :
      couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff n first ≤
        couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff n second := by
    unfold couplingParametricKCompatibleSupportEventNumerator
    apply listQSum_le_of_injective
      ((canonicalCompatibleAmbientFamilies n).filter first)
      ((canonicalCompatibleAmbientFamilies n).filter second)
      (couplingParametricKSupportFamilyActivity coupling cutoff n)
      (couplingParametricKSupportFamilyActivity coupling cutoff n)
      (fun family => family)
    · exact List.filter_sublist.nodup
        (canonicalCompatibleAmbientFamilies_nodup n)
    · intro family hfamily
      have hparts := List.mem_filter.mp hfamily
      exact List.mem_filter.mpr
        ⟨hparts.1, himp family hparts.1 hparts.2⟩
    · intro left _ right _ heq
      exact heq
    · intro family _
      exact Q'.le_refl' _
    · intro family _
      exact couplingParametricKSupportFamilyActivity_nonnegative
        hcoupling cutoff n family
  unfold couplingParametricKCompatibleSupportEventProbability Q'.divPos
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ hnumerator
    (Q'.le_of_lt
      (Q'.recipPos_pos
        (couplingParametricKCompatibleSupportGasPartition
          coupling cutoff n)
        (couplingParametricKCompatibleSupportGasPartition_pos
          hcoupling cutoff n)))

theorem couplingParametricKPinnedLargeFamilyEventProbability_le_activity
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n face sizeFloor : Nat) :
    couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff n
        (canonicalPinnedLargeFamilyEvent face sizeFloor) ≤
      couplingParametricKCanonicalPinnedLargeActivity
        coupling cutoff n face sizeFloor := by
  have hnumerator := markedEventNumerator_le_activitySum_mul_partition
    (canonicalPolymerCompatibleB n)
    (couplingParametricKSupportActivity coupling cutoff n)
    (couplingParametricKSupportActivity_nonnegative
      hcoupling cutoff n)
    (canonicalPinnedLargeMark face sizeFloor)
    (canonicalSurfacePolymers n)
  apply Q'.divPos_le_of_le_mul
  have hnumEq := genericCouplingParametricKEventNumerator_eqv
    coupling cutoff n (canonicalPinnedLargeFamilyEvent face sizeFloor)
  have hpartitionEq := genericCouplingParametricKPartition_eqv
    coupling cutoff n
  have hrightEq :
      couplingParametricKCanonicalPinnedLargeActivity
          coupling cutoff n face sizeFloor *
        partition (canonicalPolymerCompatibleB n)
          (couplingParametricKSupportActivity coupling cutoff n)
          (canonicalSurfacePolymers n) ≈
      couplingParametricKCanonicalPinnedLargeActivity
          coupling cutoff n face sizeFloor *
        couplingParametricKCompatibleSupportGasPartition
          coupling cutoff n :=
    Q'.mul_eqv_congr_left _ _ _ hpartitionEq
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hnumEq)
    (Q'.le_trans' _ _ _ hnumerator (Q'.le_of_eqv hrightEq))

/-- The complete spin-summed law inherits the anchor geometric tail at every
explicit coupling in the proved strong-coupling interval. -/
theorem couplingParametricKPinnedLargeFamilyEventProbability_le_tail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (cutoff n face sizeFloor : Nat) :
    couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff n
        (canonicalPinnedLargeFamilyEvent face sizeFloor) ≤
      Q'.ofNat 2 * anchorDecoratedEffectiveRatio ^ sizeFloor := by
  exact Q'.le_trans' _ _ _
    (couplingParametricKPinnedLargeFamilyEventProbability_le_activity
      hcoupling cutoff n face sizeFloor)
    (couplingParametricKCanonicalPinnedLargeActivity_le_tail
      hcoupling hle cutoff n face sizeFloor)

theorem couplingParametricKFaceTruncationRemainderProbability_le_tail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (cutoff n face sizeFloor : Nat) :
    couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff n
        (canonicalFaceTruncationRemainderEvent n face sizeFloor) ≤
      Q'.ofNat 2 * anchorDecoratedEffectiveRatio ^ sizeFloor := by
  exact Q'.le_trans' _ _ _
    (couplingParametricKCompatibleSupportEventProbability_mono
      hcoupling cutoff n _ _
      (fun _family hfamily hremainder =>
        canonicalFaceTruncationRemainder_implies_large
          hfamily hremainder))
    (couplingParametricKPinnedLargeFamilyEventProbability_le_tail
      hcoupling hle cutoff n face sizeFloor)

#print axioms couplingParametricKCanonicalPinnedLargeActivity_le_anchor
#print axioms couplingParametricKCanonicalPinnedLargeActivity_le_tail
#print axioms couplingParametricKCompatibleSupportEventProbability_mono
#print axioms couplingParametricKPinnedLargeFamilyEventProbability_le_tail
#print axioms couplingParametricKFaceTruncationRemainderProbability_le_tail

end YMGap.Continuum.Z4CouplingParametricCanonicalFaceEventPinnedTail
