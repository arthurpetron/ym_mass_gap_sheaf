/-
# Descent-count spatial decay for the SAME original action

The original connecting-core family now has entropy factor 96, with its
exact old codes and signed expansion unchanged. This gives a connected
numerator bound whenever 96*adjustedCoreRate < 1. Under the OLD 625-rate
guard, a common comparison core rate 1/384 gives spatial decay (1/4)^d,
even when the old entropy upper bound approaches one.

The probe/collar amplitude retains its coupling dependence and the SAME
actual partition square. The common spatial rate is not yet a theorem on
the completed transfer or a continuum survival obstruction: that join must
be proved on the original centered moments, not asserted by renaming rates.
-/
import YMGap.Continuum.BF4ExactSlabDescentCoreCount
import YMGap.Continuum.BF4ExactSlabHeterogeneousDistanceDecay

namespace YMGap.Continuum.BF4ExactSlabDescentDistanceDecay

set_option autoImplicit false
open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount
  (connectingAnchors connecting_selected connecting_nodup)
open YMGap.Continuum.BF4ExactSlabDescentCoreCount (countPrefactor connectingAtSize_length_le)
open YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay (minimumCoreSize connecting_core_size_floor)
open YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion
open YMGap.Continuum.BF4ExactSlabHeterogeneousRootedResummation
open YMGap.Continuum.BF4ExactSlabHeterogeneousDistanceDecay (resummed_geometric_bound)
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal (ProbeCarrier)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.FiniteWeightedGramSOS (listQSum_mul_right)
open YMGap.Continuum.FiniteDeterministicKernelPushforward (listQSum_mul_left)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

theorem connecting_weight_tail {rate : Q'} (hr : (0 : Q') ≤ rate) (hs : entropyRate 96 rate < 1)
    {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (extent : Nat) (ambient : List Nat) (d : Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (hsize : ∀ ids, ids ∈ connectingAnchors extent left right ambient → d ≤ ids.length) :
    listQSum (fun ids => rate^ids.length) (connectingAnchors extent left right ambient) ≤
      tailBudget (countPrefactor P Q) 96 d rate hs := by
  apply size_sum_bound _ List.length (countPrefactor P Q) 96 d ambient.length hr hs hsize
  · intro ids hi
    exact (selected_sublist (connecting_selected hi)).length_le
  · intro n
    have he : (connectingAnchors extent left right ambient).filter (fun ids => decide (n=ids.length)) =
        (connectingAnchors extent left right ambient).filter (fun ids => decide (ids.length=n)) := by
      apply List.filter_congr
      intro ids _
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using (eq_comm : n=ids.length ↔ ids.length=n)
    rw [he]
    exact connectingAtSize_length_le P Q extent ambient n hn hphys

/-- A fixed rational core majorant inside the improved entropy region. -/
def comparisonCoreRate : Q' := Q'.mkPos 1 384 (by decide)

theorem comparison_entropy : entropyRate 96 comparisonCoreRate ≈ Q'.mkPos 1 4 (by decide) := by decide
theorem comparison_nonnegative : (0 : Q') ≤ comparisonCoreRate := by decide
theorem comparison_guard : entropyRate 96 comparisonCoreRate < 1 := by decide

/-- The old strict guard leaves a nonzero entropy margin after recoding. -/
theorem oldGuard_coreRate_le {rate : Q'} (hs : entropyRate 625 rate < 1) :
    rate ≤ comparisonCoreRate := by
  exact Q'.le_of_mul_le_mul_left (c := (625 : Q'))
    (Q'.le_trans' _ _ _ (Q'.le_of_lt hs) (by decide : (1 : Q') ≤ 625*comparisonCoreRate))
    (by decide)

private theorem abs_sum_bound {A : Type} (f g : A → Q') : ∀ xs : List A,
    (∀ x, x ∈ xs → Q'.abs (f x) ≤ g x) → Q'.abs (listQSum f xs) ≤ listQSum g xs
  | [], _ => by change Q'.abs (0 : Q') ≤ 0; decide
  | x::xs, h => Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
    (Q'.add_le_add (h x List.mem_cons_self) (abs_sum_bound f g xs (fun y hy => h y (List.mem_cons_of_mem x hy))))

/-- Explicit amplitude times the new 96-entropy geometric tail. -/
def distanceBudget {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (W : Q') (hd : heatRemainderBound W < 1) (hs : entropyRate 96 (adjustedCoreRate W hd) < 1)
    (c d : Q') : Q' :=
  ((c*d+c*d)*probePrefactor W hd (left++right).length)*
    tailBudget (countPrefactor P Q) 96 (minimumCoreSize P Q) (adjustedCoreRate W hd) hs

/-- The spatial exponent has a fixed rate 1/4, not the old coupling-dependent
entropy rate. Only the displayed probe/collar amplitude retains W. -/
def oldGuardBudget {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (W : Q') (hd : heatRemainderBound W < 1) (c d : Q') : Q' :=
  ((c*d+c*d)*probePrefactor W hd (left++right).length)*
    tailBudget (countPrefactor P Q) 96 (minimumCoreSize P Q) comparisonCoreRate comparison_guard

variable (w : Nat → Q') (K : Nat → Nat) (extent : Nat) {W : Q'}
  (hW0 : (0 : Q') ≤ W) (hW1 : W ≤ (1 : Q'))
  (hw0 : ∀ id, id ∈ slabPhysicalFaceEdges extent → (0 : Q') ≤ w id)
  (hwW : ∀ id, id ∈ slabPhysicalFaceEdges extent → w id ≤ W)
  (hsmall : heatRatio W ≤ HalfPow.half) (hd : heatRemainderBound W < 1)

include hW0 hW1 hw0 hwW hsmall hd in
private theorem connected_of_weight_bound
    (p q : RatPoly) (c d : Q') (Ip : Interval (blocks extent) p c) (Iq : Interval (blocks extent) q d)
    (left right : List Z4Link) (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)
    (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) (budget : Q')
    (hb : listQSum (fun ids => (adjustedCoreRate W hd)^ids.length)
      (connectingAnchors extent left right ambient) ≤ budget) :
    Q'.abs (connectedNumerator w K extent ambient p q) ≤
      (((c*d+c*d)*probePrefactor W hd (left++right).length)*budget)*partitionSquare w K extent ambient := by
  let r := adjustedCoreRate W hd
  let A := (c*d+c*d)*probePrefactor W hd (left++right).length
  let Z := partitionSquare w K extent ambient
  let anchors := connectingAnchors extent left right ambient
  have hsum : Q'.abs (listQSum (fun ids => connectedCoefficient w K extent p q ids *
      partitionSquare w K extent (detachedIds extent (left++right) ids ambient)) anchors) ≤
      listQSum (fun ids => (A*r^ids.length)*Z) anchors := by
    apply abs_sum_bound
    intro ids hi
    exact resummed_geometric_bound w K extent hW0 hW1 hw0 hwW hsmall hd p q c d (left++right) Ip Iq
      ambient ids hn hphys (connecting_selected hi)
  have hfactor : listQSum (fun ids => (A*r^ids.length)*Z) anchors ≈
      (A*listQSum (fun ids => r^ids.length) anchors)*Z :=
    Q'.eqv_trans _ _ _ (listQSum_mul_right _ Z anchors)
      (Q'.mul_eqv_congr_right _ _ Z (listQSum_mul_left A _ anchors))
  have ha : (0 : Q') ≤ A := Q'.mul_nonneg _ _
    (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ Ip.nonnegative Iq.nonnegative)
      (Q'.mul_nonneg _ _ Ip.nonnegative Iq.nonnegative)) (probePrefactor_nonnegative W hd _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr
    (connectedNumerator_connecting_expansion w K extent p q left right Ip.support Iq.support hl hr ambient hn)))
    (Q'.le_trans' _ _ _ hsum (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
      (Q'.mul_le_mul_of_nonneg_right _ _ Z (Q'.mul_le_mul_of_nonneg_left _ _ A hb ha)
        (SumOfSquares.q_mul_self_nonneg _))))

include hW0 hW1 hw0 hwW hsmall hd in
/-- Actual heterogeneous original action, with the enlarged 96-rate guard. -/
theorem connectedNumerator_distance_bound (hs : entropyRate 96 (adjustedCoreRate W hd) < 1)
    (p q : RatPoly) (c d : Q') (Ip : Interval (blocks extent) p c) (Iq : Interval (blocks extent) q d)
    (left right : List Z4Link) (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)
    (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    Q'.abs (connectedNumerator w K extent ambient p q) ≤
      distanceBudget P Q W hd hs c d * partitionSquare w K extent ambient :=
  connected_of_weight_bound w K extent hW0 hW1 hw0 hwW hsmall hd p q c d Ip Iq left right hl hr ambient hn hphys _
    (connecting_weight_tail (adjustedCoreRate_nonnegative hW0 hd) hs P Q extent ambient (minimumCoreSize P Q)
      hn hphys (connecting_core_size_floor P Q extent ambient hn hphys))

include hW0 hW1 hw0 hwW hsmall hd in
/-- A uniform spatial rate on the ENTIRE old guard, including sequences
whose old 625-rate tends to one. This is still a finite-numerator theorem. -/
theorem oldGuard_distance_bound (hs : entropyRate 625 (adjustedCoreRate W hd) < 1)
    (p q : RatPoly) (c d : Q') (Ip : Interval (blocks extent) p c) (Iq : Interval (blocks extent) q d)
    (left right : List Z4Link) (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)
    (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    Q'.abs (connectedNumerator w K extent ambient p q) ≤
      oldGuardBudget P Q W hd c d * partitionSquare w K extent ambient := by
  apply connected_of_weight_bound w K extent hW0 hW1 hw0 hwW hsmall hd p q c d Ip Iq left right hl hr ambient hn hphys
  exact Q'.le_trans' _ _ _ (sum_le_on _ _ _ (fun ids _ =>
    CRealLog.pow_le_pow_base _ _ (adjustedCoreRate_nonnegative hW0 hd) (oldGuard_coreRate_le hs) ids.length))
    (connecting_weight_tail comparison_nonnegative comparison_guard P Q extent ambient (minimumCoreSize P Q)
      hn hphys (connecting_core_size_floor P Q extent ambient hn hphys))

end YMGap.Continuum.BF4ExactSlabDescentDistanceDecay

#print axioms YMGap.Continuum.BF4ExactSlabDescentDistanceDecay.connecting_weight_tail
#print axioms YMGap.Continuum.BF4ExactSlabDescentDistanceDecay.comparisonCoreRate
#print axioms YMGap.Continuum.BF4ExactSlabDescentDistanceDecay.comparison_entropy
#print axioms YMGap.Continuum.BF4ExactSlabDescentDistanceDecay.comparison_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabDescentDistanceDecay.comparison_guard
#print axioms YMGap.Continuum.BF4ExactSlabDescentDistanceDecay.oldGuard_coreRate_le
#print axioms YMGap.Continuum.BF4ExactSlabDescentDistanceDecay.distanceBudget
#print axioms YMGap.Continuum.BF4ExactSlabDescentDistanceDecay.oldGuardBudget
#print axioms YMGap.Continuum.BF4ExactSlabDescentDistanceDecay.connectedNumerator_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabDescentDistanceDecay.oldGuard_distance_bound
