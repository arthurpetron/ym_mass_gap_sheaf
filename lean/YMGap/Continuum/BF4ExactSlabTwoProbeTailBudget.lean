/-
# ORIGINAL connected numerator: cutoff/volume-independent core-size tail

The signed spectator sum is performed before taking absolute values.
The original local collar-removal floor controls its partition square
relative to the SAME full partition square. The new two-probe count then
sums the actual retained cores with rate s(w)=625*adjustedCoreRate(w).

For a supplied geometric lower size d, the coefficient has s(w)^d and
depends only on w, the two observable bounds and their two carrier sizes
and link counts. It does not depend on cutoff, ambient volume or probe
separation. The existing nome 1/1024 satisfies the rate guard.

The geometric size floor, normalized cutoff/thermodynamic passage and the
resulting temporal decay/gap are not asserted by this size-tail theorem.
-/

import YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount
import YMGap.Continuum.BF4ExactSlabResummedCoefficientBound
import YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
import YMGap.Continuum.BF4ExactSlabSummableCoreRate

namespace YMGap.Continuum.BF4ExactSlabTwoProbeTailBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal (ProbeCarrier)
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount
open YMGap.Continuum.BF4ExactSlabRootedSelection
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabResummedCoefficientBound
open YMGap.Continuum.BF4ExactSlabRelativePartitionBound
open YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabMixedAction
open YMGap.Continuum.BF4ExactSlabMixedCoefficientBound
open YMGap.Continuum.BF4ExactSlabMixedRelativePartition
open YMGap.Continuum.BF4ExactSlabMixedFiniteBoundaryBudget
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

theorem allInside_weight (w : Q') : ∀ ids : List Nat,
    mixedHeatWeight w (fun _ => true) ids = (pairedHeatRate w)^ids.length
  | [] => rfl
  | _ :: ids => congrArg (fun r => pairedHeatRate w*r) (allInside_weight w ids)

theorem allInside_floor (w : Q') (ids : List Nat) :
    mixedRemovalFloor w (fun _ => true) ids = removalFloor w ids.length * removalFloor w ids.length := by
  have hi : inside (fun _ => true) ids = ids := List.filter_eq_self.mpr (fun _ _ => rfl)
  unfold mixedRemovalFloor
  rw [hi]

private theorem remove_positive_factor {R x b : Q'} (hR : (0 : Q') < R) (h : R*x ≤ b) :
    x ≤ Q'.recipPos R hR*b := by
  let i := Q'.recipPos R hR
  have hi : i*R ≈ 1 := Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv R hR)
  have he : i*(R*x) ≈ x := Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv i R x))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ x hi) (Q'.one_mul_eqv x))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (Q'.mul_le_mul_of_nonneg_left _ _ i h (Q'.le_of_lt (Q'.recipPos_pos R hR)))

private theorem abs_sum_bound {A : Type} (f g : A → Q') : ∀ xs : List A,
    (∀ x, x ∈ xs → Q'.abs (f x) ≤ g x) → Q'.abs (listQSum f xs) ≤ listQSum g xs
  | [], _ => by change Q'.abs (0 : Q') ≤ 0; decide
  | x :: xs, h => Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.add_le_add (h x List.mem_cons_self) (abs_sum_bound f g xs (fun y hy => h y (List.mem_cons_of_mem x hy))))

theorem resummed_geometric_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (K extent : Nat) (p q : RatPoly) (c d : Q') (links : List Z4Link)
    (P : Interval (boundaryCompleteSlabLinks extent).length p c)
    (Q : Interval (boundaryCompleteSlabLinks extent).length q d)
    (hlp : LinkLocal extent links p) (hlq : LinkLocal extent links q) (ambient anchor : List Nat)
    (hn : ambient.Nodup) (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (ha : anchor ∈ selections ambient) :
    Q'.abs (connectedCoefficient w K extent p q anchor *
      partitionSquare w K extent (detachedIds extent links anchor ambient)) ≤
      (((c*d+c*d)*probePrefactor w hd links.length)*(adjustedCoreRate w hd)^anchor.length)*
        partitionSquare w K extent ambient := by
  let R := mixedRemovalFloor w (fun _ => true) (collarIds extent links anchor ambient)
  let hR := mixedRemovalFloor_pos hd (fun _ => true) (collarIds extent links anchor ambient)
  let i := Q'.recipPos R hR
  let Z := partitionSquare w K extent ambient
  have hclear : R*Q'.abs (spectatorSum w K extent p q anchor (detachedIds extent links anchor ambient)) ≤
      anchorCap w c d anchor.length*Z := by
    dsimp only [R]
    rw [allInside_floor]
    exact detached_cleared_bound hw0 hw1 hsmall (Q'.le_of_lt hd) K extent p q c d links P Q hlp hlq anchor ambient
      (fun id hi => hphys id (selected_mem ha id hi)) hphys
  have hrel : Q'.abs (spectatorSum w K extent p q anchor (detachedIds extent links anchor ambient)) ≤
      ((c*d+c*d)*normalizedCoreWeight w hd extent links (fun _ => true) ambient anchor)*Z := by
    unfold normalizedCoreWeight
    rw [allInside_weight]
    exact Q'.le_trans' _ _ _ (remove_positive_factor hR hclear) (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
        (.mul (.mul (.var 1) (.mul (.var 2) (.var 0))) (.var 3)) (by decide)
        (fun | 0 => i | 1 => c*d+c*d | 2 => (pairedHeatRate w)^anchor.length | _ => Z)))
  have hz : (0 : Q') ≤ Z := SumOfSquares.q_mul_self_nonneg _
  have hc : (0 : Q') ≤ c*d+c*d := Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ P.nonnegative Q.nonnegative)
    (Q'.mul_nonneg _ _ P.nonnegative Q.nonnegative)
  have hg := Q'.mul_le_mul_of_nonneg_right _ _ Z
    (Q'.mul_le_mul_of_nonneg_left _ _ (c*d+c*d)
      (normalizedCoreWeight_geometric_bound hw0 hd extent links (fun _ => true) ambient anchor hn hphys) hc) hz
  have hpin := spectatorSum_pin w K extent p q links P.support Q.support hlp hlq anchor
    (detachedIds extent links anchor ambient) (detached_disjoint extent links anchor ambient)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_eqv_congr hpin))
    (Q'.le_trans' _ _ _ hrel (Q'.le_trans' _ _ _ hg (Q'.ge_of_eqv
      (Q'.mul_eqv_congr_right _ _ Z (Q'.mul_assoc_eqv _ _ _)))))

theorem connecting_weight_tail {rate : Q'} (hr : (0 : Q') ≤ rate) (hs : entropyRate 625 rate < 1)
    {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (extent : Nat) (ambient : List Nat) (d : Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (hsize : ∀ ids, ids ∈ connectingAnchors extent left right ambient → d ≤ ids.length) :
    listQSum (fun ids => rate^ids.length) (connectingAnchors extent left right ambient) ≤
      tailBudget (countPrefactor P Q) 625 d rate hs := by
  apply size_sum_bound _ List.length (countPrefactor P Q) 625 d ambient.length hr hs hsize
  · intro ids hi
    exact (selected_sublist (connecting_selected hi)).length_le
  · intro n
    have he : (connectingAnchors extent left right ambient).filter (fun ids => decide (n = ids.length)) =
        (connectingAnchors extent left right ambient).filter (fun ids => decide (ids.length = n)) := by
      apply List.filter_congr
      intro ids _
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using (eq_comm : n = ids.length ↔ ids.length = n)
    rw [he]
    exact connectingAtSize_length_le P Q extent ambient n hn hphys

def twoProbeBudget {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (w : Q') (hd : heatRemainderBound w < 1) (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (c d : Q') (minimumSize : Nat) : Q' :=
  ((c*d+c*d)*probePrefactor w hd (left++right).length)*
    tailBudget (countPrefactor P Q) 625 minimumSize (adjustedCoreRate w hd) hs

/-- SAME full partition square; the prefactor has no volume/cutoff/separation parameter. -/
theorem connectedNumerator_tail_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (K extent : Nat) (p q : RatPoly) (c d : Q')
    (Ip : Interval (boundaryCompleteSlabLinks extent).length p c)
    (Iq : Interval (boundaryCompleteSlabLinks extent).length q d)
    (left right : List Z4Link) (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)
    (ambient : List Nat) (minimumSize : Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (hsize : ∀ ids, ids ∈ connectingAnchors extent left right ambient → minimumSize ≤ ids.length) :
    Q'.abs (connectedNumerator w K extent ambient p q) ≤
      twoProbeBudget P Q w hd hs c d minimumSize * partitionSquare w K extent ambient := by
  let r := adjustedCoreRate w hd
  let A := (c*d+c*d)*probePrefactor w hd (left++right).length
  let Z := partitionSquare w K extent ambient
  let anchors := connectingAnchors extent left right ambient
  have hsum : Q'.abs (listQSum (fun ids => connectedCoefficient w K extent p q ids *
      partitionSquare w K extent (detachedIds extent (left++right) ids ambient)) anchors) ≤
      listQSum (fun ids => (A*r^ids.length)*Z) anchors := by
    apply abs_sum_bound
    intro ids hi
    exact resummed_geometric_bound hw0 hw1 hsmall hd K extent p q c d (left++right) Ip Iq
      (hl.mono (fun _ h => List.mem_append.mpr (Or.inl h)))
      (hr.mono (fun _ h => List.mem_append.mpr (Or.inr h))) ambient ids hn hphys (connecting_selected hi)
  have hfactor : listQSum (fun ids => (A*r^ids.length)*Z) anchors ≈
      (A*listQSum (fun ids => r^ids.length) anchors)*Z :=
    Q'.eqv_trans _ _ _ (listQSum_mul_right _ Z anchors)
      (Q'.mul_eqv_congr_right _ _ Z (listQSum_mul_left A _ anchors))
  have ha : (0 : Q') ≤ A := Q'.mul_nonneg _ _
    (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ Ip.nonnegative Iq.nonnegative)
      (Q'.mul_nonneg _ _ Ip.nonnegative Iq.nonnegative)) (probePrefactor_nonnegative w hd _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr
    (connectedNumerator_connecting_expansion w K extent p q left right Ip.support Iq.support hl hr ambient hn)))
    (Q'.le_trans' _ _ _ hsum (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
      (Q'.mul_le_mul_of_nonneg_right _ _ Z (Q'.mul_le_mul_of_nonneg_left _ _ A
        (connecting_weight_tail (adjustedCoreRate_nonnegative hw0 hd) hs P Q extent ambient minimumSize hn hphys hsize) ha)
        (SumOfSquares.q_mul_self_nonneg _))))

end YMGap.Continuum.BF4ExactSlabTwoProbeTailBudget

#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeTailBudget.allInside_weight
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeTailBudget.allInside_floor
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeTailBudget.resummed_geometric_bound
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeTailBudget.connecting_weight_tail
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeTailBudget.twoProbeBudget
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeTailBudget.connectedNumerator_tail_bound
