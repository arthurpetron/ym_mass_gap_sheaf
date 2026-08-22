/-
# Persistence of physical BF4 support edges under cutoff enlargement

The unnormalized reflected production kernel is entrywise nonnegative.  If
an entry between two old bounded states is nonzero, it is therefore positive.
The exact cylinder-numerator cutoff decomposition writes its value at every
larger representation cutoff as the old positive numerator plus a
nonnegative new-label increment.  Hence the same support edge survives.

This is qualitative support persistence, not equality of kernel entries or a
uniform quantitative lower bound.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffPositiveRowPersistence

namespace YMGap.Continuum.BF4PhysicalCutoffKernelSupportPersistence

set_option maxRecDepth 100000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem centralHalfStates_mem_of_le_local
    {base later half : Nat} (hcutoff : base ≤ later)
    {state : EdgeLabelling}
    (hstate : state ∈ centralHalfStates base half) :
    state ∈ centralHalfStates later half := by
  unfold centralHalfStates at hstate ⊢
  have hsound := boundedEdgeLabellings_sound
    base (centralLowerFaceIds half) state hstate
  apply boundedEdgeLabellings_complete
  · intro id hid
    have hbound := hsound.1 id hid
    omega
  · exact hsound.2

/-- Every unnormalized reflected production-kernel entry is nonnegative. -/
theorem centralPhysicalReflectedKernel_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) (left right : EdgeLabelling) :
    (0 : Q') ≤ centralPhysicalReflectedKernel w K half left right := by
  unfold centralPhysicalReflectedKernel
  apply listQSum_nonnegative_on
  intro boundary _
  exact slabParametricKPhysicalTerm_nonnegative
    hw K (centralExtent half)
    (assembleReflectedSlabLabelling half left boundary right)

private theorem q_pos_of_nonnegative_not_eqv_zero
    {q : Q'} (hq0 : (0 : Q') ≤ q) (hqne : ¬ q ≈ 0) :
    (0 : Q') < q := by
  have hnum0 : (0 : Int) ≤ q.num :=
    (Q'.zero_le_iff_num_nonneg q).mp hq0
  have hnumne : q.num ≠ 0 := by
    intro hnum
    apply hqne
    show q.num * (1 : Int) = (0 : Int) * (q.den : Int)
    simp [hnum]
  show (0 : Int) * (q.den : Int) < q.num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  omega

private theorem pos_not_eqv_zero_local {q : Q'}
    (hq : (0 : Q') < q) : ¬ q ≈ 0 := by
  intro hzero
  exact (Int.not_lt_of_ge (Q'.le_of_eqv hzero)) hq

/-- Strict positivity of one old production-kernel entry persists at every
larger representation cutoff. -/
theorem centralPhysicalReflectedKernel_pos_of_le
    {w : Q'} (hw : (0 : Q') ≤ w)
    {base later half : Nat} (hcutoff : base ≤ later)
    {source target : EdgeLabelling}
    (hsource : source ∈ centralHalfStates base half)
    (htarget : target ∈ centralHalfStates base half)
    (hpositive : (0 : Q') <
      centralPhysicalReflectedKernel w base half source target) :
    (0 : Q') <
      centralPhysicalReflectedKernel w later half source target := by
  have hsourceLater : source ∈ centralHalfStates later half :=
    centralHalfStates_mem_of_le_local hcutoff hsource
  have htargetLater : target ∈ centralHalfStates later half :=
    centralHalfStates_mem_of_le_local hcutoff htarget
  let observable := centralPairCylinderObservable half source target
  have hbaseNumeratorPositive :
      (0 : Q') < slabBoundedObservableNumerator
        w base (centralExtent half) observable := by
    have heq := centralPairCylinderNumerator_eq_physicalKernel
      (w := w) hsource htarget
    exact Q'.pos_of_lt_of_le hpositive (Q'.ge_of_eqv heq)
  have hincrementNonnegative :
      (0 : Q') ≤ slabBoundedObservableCutoffIncrement
        w base later (centralExtent half) observable :=
    slabBoundedObservableCutoffIncrement_nonnegative
      hw base later (centralExtent half) observable
  have hlaterNumeratorPositive :
      (0 : Q') < slabBoundedObservableNumerator
        w later (centralExtent half) observable := by
    have hdecomposition :=
      slabBoundedObservableNumerator_eq_base_add_increment
        (w := w) hcutoff observable
    refine Q'.pos_of_lt_of_le hbaseNumeratorPositive ?_
    refine Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ _ hincrementNonnegative) ?_
    exact Q'.ge_of_eqv hdecomposition
  have heq := centralPairCylinderNumerator_eq_physicalKernel
    (w := w) hsourceLater htargetLater
  exact Q'.pos_of_lt_of_le hlaterNumeratorPositive
    (Q'.le_of_eqv heq)

/-- A nonzero old production-kernel entry remains nonzero at every larger
cutoff. -/
theorem centralPhysicalReflectedKernel_not_eqv_zero_of_le
    {w : Q'} (hw : (0 : Q') ≤ w)
    {base later half : Nat} (hcutoff : base ≤ later)
    {source target : EdgeLabelling}
    (hsource : source ∈ centralHalfStates base half)
    (htarget : target ∈ centralHalfStates base half)
    (hnonzero : ¬
      centralPhysicalReflectedKernel w base half source target ≈ 0) :
    ¬ centralPhysicalReflectedKernel w later half source target ≈ 0 := by
  have hpositive : (0 : Q') <
      centralPhysicalReflectedKernel w base half source target :=
    q_pos_of_nonnegative_not_eqv_zero
      (centralPhysicalReflectedKernel_nonnegative
        hw base half source target)
      hnonzero
  exact pos_not_eqv_zero_local
    (centralPhysicalReflectedKernel_pos_of_le
      hw hcutoff hsource htarget hpositive)

end YMGap.Continuum.BF4PhysicalCutoffKernelSupportPersistence

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffKernelSupportPersistence.centralPhysicalReflectedKernel_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffKernelSupportPersistence.centralPhysicalReflectedKernel_pos_of_le
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffKernelSupportPersistence.centralPhysicalReflectedKernel_not_eqv_zero_of_le
