/-
# Normalized original boundary response for any physical face mask

The existing same-cutoff mixed determinant bound retains the product of
the full and masked original partitions. Their ACTUAL finite reciprocals
cancel exactly before taking the cutoff limit. The original core-size tail
estimate therefore bounds the difference of the two constructed normalized
expectations at any slab extent, without a volume-dependent reciprocal
ceiling in the final coefficient and without an odd/even restriction.

No geometric separation is invented: the last theorem requires the stated
finite lower bound on active-core sizes. Supplying the actual parity-changing
slab mask, its original-observable pin and its growing separation remains
the next step. This is boundary response, not a time-correlation or physical
mass-gap estimate; no completed T1, range or continuum/Clay closure follows.
-/

import YMGap.Continuum.BF4ExactSlabFaceSetExpectation
import YMGap.Continuum.BF4ExactSlabUniformCoreBudget
import YMGap.Constructive.CRealAbsContinuity

namespace YMGap.Continuum.BF4ExactSlabFaceSetBoundaryComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabMixedAction
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion
open YMGap.Continuum.BF4ExactSlabUniformCoreBudget
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem cancel_partitions (b X Y r s : Q') (hx : X*r ≈ 1) (hy : Y*s ≈ 1) :
    ((b*(X*Y))*r)*s ≈ b :=
  Q'.eqv_trans _ _ _ (RingNormaliser.poly_identity_of_normal_eq
    (.mul (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3)) (.var 4))
    (.mul (.var 0) (.mul (.mul (.var 1) (.var 3)) (.mul (.var 2) (.var 4)))) (by decide)
    (fun | 0 => b | 1 => X | 2 => Y | 3 => r | _ => s))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left b _ _
      (Q'.eqv_trans _ _ _ (qmul hx hy) (Q'.one_mul_eqv _))) (Q'.mul_one_eqv _))

private theorem ratio_difference_bound (a b X Y cap : Q') (hX : (0 : Q') < X) (hY : (0 : Q') < Y)
    (h : Q'.abs (a*Y + -(b*X)) ≤ cap*(X*Y)) :
    Q'.abs (a*Q'.recipPos X hX + -(b*Q'.recipPos Y hY)) ≤ cap := by
  let r := Q'.recipPos X hX
  let s := Q'.recipPos Y hY
  have hr : (0 : Q') ≤ r := Q'.le_of_lt (Q'.recipPos_pos _ _)
  have hs : (0 : Q') ≤ s := Q'.le_of_lt (Q'.recipPos_pos _ _)
  have hx : X*r ≈ 1 := Q'.mul_recipPos_eqv _ _
  have hy : Y*s ≈ 1 := Q'.mul_recipPos_eqv _ _
  have he : ((a*Y + -(b*X))*r)*s ≈ a*r + -(b*s) :=
    Q'.eqv_trans _ _ _ (RingNormaliser.poly_identity_of_normal_eq
      (.mul (.mul (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2)))) (.var 4)) (.var 5))
      (.add (.mul (.mul (.var 0) (.var 4)) (.mul (.var 3) (.var 5)))
        (.neg (.mul (.mul (.var 1) (.var 5)) (.mul (.var 2) (.var 4))))) (by decide)
      (fun | 0 => a | 1 => b | 2 => X | 3 => Y | 4 => r | _ => s))
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hy) (Q'.mul_one_eqv _))
        (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hx) (Q'.mul_one_eqv _))))
  have houter := ExpNeg.abs_mul_le ((a*Y + -(b*X))*r) s
  have hinner := ExpNeg.abs_mul_le (a*Y + -(b*X)) r
  rw [ExpNeg.abs_of_nonneg hs] at houter
  rw [ExpNeg.abs_of_nonneg hr] at hinner
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_eqv_congr he))
    (Q'.le_trans' _ _ _ houter
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hinner hs)
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ h hr) hs)
          (Q'.le_of_eqv (cancel_partitions cap X Y r s hx hy)))))

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (extent : Nat) (ids : List Nat) (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
  (keep : Nat → Bool)

local notation "kept" => inside keep ids
local notation "keptPhysical" => (fun id hi => hids id (And.left (List.mem_filter.mp hi)))
local notation "fullValue" => finiteValue w hw0 hw1 hsmall hd extent ids hids
local notation "keptValue" => finiteValue w hw0 hw1 hsmall hd extent kept keptPhysical
local notation "fullMean" => expectation w hw0 hw1 hsmall hd extent ids hids
local notation "keptMean" => expectation w hw0 hw1 hsmall hd extent kept keptPhysical

/-- Both actual partitions cancel before any volume-dependent floor is estimated. -/
theorem finite_mask_bound (p : RatPoly) (b : Q') (K : Nat)
    (h : Q'.abs (mixedNumerator w K extent keep p ids) ≤ b*mixedPartition w K extent keep ids) :
    Q'.abs (fullValue p K + -(keptValue p K)) ≤ b :=
  ratio_difference_bound _ _ _ _ b
    (Q'.pos_of_lt_of_le (partitionFloor_pos hd ids) (partition_floor w hw0 hw1 hsmall hd extent ids hids K))
    (Q'.pos_of_lt_of_le (partitionFloor_pos hd kept) (partition_floor w hw0 hw1 hsmall hd extent kept keptPhysical K)) h

/-- Same original normalized cutoff limits, with the SAME finite-bound coefficient. -/
theorem mask_bound (p : RatPoly) (b : Q')
    (h : ∀ K, Q'.abs (mixedNumerator w K extent keep p ids) ≤ b*mixedPartition w K extent keep ids) :
    leEv (CReal.abs (CReal.sub (fullMean p) (keptMean p))) (ofQ' b) :=
  leEv_of_convergesTo_le
    (convergesTo_abs (convergesTo_add
      (finite_converges w hw0 hw1 hsmall hd extent ids hids p)
      (TrigAddCReal.convergesTo_neg (finite_converges w hw0 hw1 hsmall hd extent kept keptPhysical p))))
    (convergesTo_const _)
    (fun K => leEv_le_ofQ'_of_approx_le
      (fun _ => finite_mask_bound w hw0 hw1 hsmall hd extent ids hids keep p b K (h K)))

/-- Existing signed core decay now reaches arbitrary-mask normalized expectations.
The only separation premise is the displayed finite active-core size bound. -/
theorem mask_tail_bound (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (p : RatPoly) (c : Q') (P : Interval (boundaryCompleteSlabLinks extent).length p c)
    (links : List Z4Link) (probe : ProbeCarrier links) (hl : LinkLocal extent links p)
    (d : Nat) (hn : ids.Nodup)
    (hsize : ∀ anchor, anchor ∈ activeAnchors extent links keep ids → d ≤ anchor.length) :
    leEv (CReal.abs (CReal.sub (fullMean p) (keptMean p)))
      (ofQ' ((c+c)*summedBoundaryBudget probe w hd hs d)) :=
  mask_bound w hw0 hw1 hsmall hd extent ids hids keep p _
    (fun K => mixedNumerator_tail_bound (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hsmall hd hs
      K extent keep p c P links probe hl ids d hn hids hsize)

end YMGap.Continuum.BF4ExactSlabFaceSetBoundaryComparison

#print axioms YMGap.Continuum.BF4ExactSlabFaceSetBoundaryComparison.finite_mask_bound
#print axioms YMGap.Continuum.BF4ExactSlabFaceSetBoundaryComparison.mask_bound
#print axioms YMGap.Continuum.BF4ExactSlabFaceSetBoundaryComparison.mask_tail_bound
