/-
# Pay fine-child entropy with the retained activity excess

The child-resolved local catalogue has 720 states, but its activity-one
sector has only eight.  This file uses that split instead of charging all
720 states at the same rate.  At `0 <= rate <= 1`, every nonminimal state has
at least one activity-excess unit and is therefore bounded by `rate^3`.
Consequently the complete one-face child catalogue has weighted mass at most

  `8 + 712 * rate^3`.

Throughout the named strong-coupling interval `rate <= 1/400`, this is
strictly below 9.  Combining that ceiling with the rooted-shape base 625 and
the two heat units reserved per component face gives the explicit effective
ratio

  `625 * rate^2 * 9`,

which is exactly `9/256 < 1` at the anchor.  Thus resolving the literal fine
children improves, rather than destroys, the paid component contraction.

Constructive contract: finite list partitioning, rational order, and the
closed child catalogue only, with the trust boundary and heartbeat budget
unchanged.
-/

import YMGap.Continuum.Z4DyadicBinaryConnectedComponentChildCode

namespace YMGap.Continuum.Z4DyadicBinaryConnectedComponentChildWeightedEntropy

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentChildCode
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentEntropyBudget
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentLocalCode
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_const_local {A : Type} (constant : Q') :
    ∀ items : List A,
      listQSum (fun _item => constant) items ≈
        Q'.ofNat items.length * constant
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv constant)
  | _head :: tail => by
      refine Q'.eqv_trans _
        (constant + Q'.ofNat tail.length * constant) _
        (Q'.add_eqv_congr_left constant _ _
          (listQSum_const_local constant tail)) ?_
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat tail.length + 1) * constant) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ constant
          (Q'.ofNat_add_eqv tail.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + (1 : Q') * constant) _
        (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 constant) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + constant) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv constant))
        (Q'.add_comm_eqv
          (Q'.ofNat tail.length * constant) constant)

private theorem listQSum_le_length_mul_local {A : Type}
    (value : A → Q') (bound : Q') : ∀ items : List A,
    (0 : Q') ≤ bound →
    (∀ item, item ∈ items → value item ≤ bound) →
      listQSum value items ≤ Q'.ofNat items.length * bound
  | [], _hbound0, _hvalue =>
      Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | head :: tail, hbound0, hvalue => by
      have htail := listQSum_le_length_mul_local value bound tail hbound0
        (fun item hitem => hvalue item (List.mem_cons_of_mem head hitem))
      have hadd := Q'.add_le_add
        (hvalue head List.mem_cons_self) htail
      exact Q'.le_trans' _ _ _ hadd
        (Q'.le_of_eqv (by
          refine Q'.eqv_symm ?_
          refine Q'.eqv_trans _
            ((Q'.ofNat tail.length + 1) * bound) _ ?_ ?_
          · exact Q'.mul_eqv_congr_right _ _ bound
              (Q'.ofNat_add_eqv tail.length 1)
          refine Q'.eqv_trans _
            (Q'.ofNat tail.length * bound + (1 : Q') * bound) _
            (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 bound) ?_
          exact Q'.eqv_trans _
            (Q'.ofNat tail.length * bound + bound) _
            (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv bound))
            (Q'.add_comm_eqv
              (Q'.ofNat tail.length * bound) bound)))

private theorem listQSum_congr_mem_local {A : Type} {f g : A → Q'} :
    ∀ items : List A, (∀ item, item ∈ items → f item ≈ g item) →
      listQSum f items ≈ listQSum g items
  | [], _h => Q'.eqv_refl 0
  | head :: tail, h => by
      change f head + listQSum f tail ≈ g head + listQSum g tail
      exact Q'.add_eqv_congr'
        (h head List.mem_cons_self)
        (listQSum_congr_mem_local tail
          (fun item hitem => h item (List.mem_cons_of_mem head hitem)))

/-! ## 1. Minimal and nonminimal local sectors -/

def finePacketComponentNonminimalChildCodes :
    List FinePacketComponentChildCode :=
  finePacketComponentChildCodes.filter fun code =>
    !(decide (code.activity = 1))

theorem finePacketComponentNonminimalChildCodes_length :
    finePacketComponentNonminimalChildCodes.length = 712 := by
  decide

def finePacketComponentChildExcessWeight
    (rate : Q') (code : FinePacketComponentChildCode) : Q' :=
  qpow rate (3 * (code.activity - 1))

def finePacketComponentChildExcessMass (rate : Q') : Q' :=
  listQSum (finePacketComponentChildExcessWeight rate)
    finePacketComponentChildCodes

def finePacketComponentChildExcessCeiling (rate : Q') : Q' :=
  Q'.ofNat 8 + Q'.ofNat 712 * qpow rate 3

private theorem finePacketComponentMinimalChildExcessMass_eqv_eight
    (rate : Q') :
    listQSum (finePacketComponentChildExcessWeight rate)
        finePacketComponentMinimalChildCodes ≈
      Q'.ofNat 8 := by
  refine Q'.eqv_trans _
    (listQSum (fun _code : FinePacketComponentChildCode => (1 : Q'))
      finePacketComponentMinimalChildCodes) _ ?_ ?_
  · apply listQSum_congr_mem_local
    intro code hcode
    have hactivity : code.activity = 1 :=
      of_decide_eq_true (List.mem_filter.mp hcode).2
    unfold finePacketComponentChildExcessWeight
    rw [hactivity]
    exact Q'.eqv_refl 1
  · refine Q'.eqv_trans _
      (Q'.ofNat finePacketComponentMinimalChildCodes.length * 1) _
      (listQSum_const_local 1 _) ?_
    rw [finePacketComponentMinimalChildCodes_length]
    exact Q'.mul_one_eqv _

/-! ## 2. One-face weighted entropy ceiling -/

theorem finePacketComponentChildExcessMass_le_ceiling
    {rate : Q'} (hrate0 : (0 : Q') ≤ rate)
    (hrate1 : rate ≤ (1 : Q')) :
    finePacketComponentChildExcessMass rate ≤
      finePacketComponentChildExcessCeiling rate := by
  have hpartition :
      finePacketComponentChildExcessMass rate ≈
        listQSum (finePacketComponentChildExcessWeight rate)
            finePacketComponentMinimalChildCodes +
          listQSum (finePacketComponentChildExcessWeight rate)
            finePacketComponentNonminimalChildCodes := by
    exact listQSum_filter_partition
      (finePacketComponentChildExcessWeight rate)
      (fun code => decide (code.activity = 1))
      finePacketComponentChildCodes
  have hminimal :
      listQSum (finePacketComponentChildExcessWeight rate)
          finePacketComponentMinimalChildCodes ≤ Q'.ofNat 8 :=
    Q'.le_of_eqv (finePacketComponentMinimalChildExcessMass_eqv_eight rate)
  have hnonminimal :
      listQSum (finePacketComponentChildExcessWeight rate)
          finePacketComponentNonminimalChildCodes ≤
        Q'.ofNat finePacketComponentNonminimalChildCodes.length *
          qpow rate 3 := by
    apply listQSum_le_length_mul_local
    · exact qpow_nonneg rate hrate0 3
    · intro code hcode
      have hparts := List.mem_filter.mp hcode
      have hcatalogue := hparts.1
      have hnotMinimal := hparts.2
      have hne : code.activity ≠ 1 := by
        intro hactivity
        simp [hactivity] at hnotMinimal
      have hadmissible : code.Admissible :=
        of_decide_eq_true (List.mem_filter.mp hcatalogue).2
      have hone : 1 ≤ code.activity :=
        code.toLocalCode.one_le_activity hadmissible.2.2
      have hexponent : 3 ≤ 3 * (code.activity - 1) := by
        omega
      unfold finePacketComponentChildExcessWeight
      exact qpow_antitone hrate0 hrate1 3
        (3 * (code.activity - 1)) hexponent
  rw [finePacketComponentNonminimalChildCodes_length] at hnonminimal
  have hadd := Q'.add_le_add hminimal hnonminimal
  unfold finePacketComponentChildExcessCeiling
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpartition) hadd

theorem finePacketComponentChildExcessCeiling_anchor_lt_nine :
    finePacketComponentChildExcessCeiling anchorCoupling <
      Q'.ofNat 9 := by
  unfold finePacketComponentChildExcessCeiling anchorCoupling qpow
  decide

theorem finePacketComponentChildExcessCeiling_lt_nine
    {rate : Q'} (hrate0 : (0 : Q') ≤ rate)
    (hrateAnchor : rate ≤ anchorCoupling) :
    finePacketComponentChildExcessCeiling rate < Q'.ofNat 9 := by
  have hpow : qpow rate 3 ≤ qpow anchorCoupling 3 :=
    qpow_mono hrate0 hrateAnchor 3
  have hscaled : Q'.ofNat 712 * qpow rate 3 ≤
      Q'.ofNat 712 * qpow anchorCoupling 3 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hpow (zero_le_ofNat 712)
  have hceiling : finePacketComponentChildExcessCeiling rate ≤
      finePacketComponentChildExcessCeiling anchorCoupling := by
    unfold finePacketComponentChildExcessCeiling
    exact Q'.add_le_add (Q'.le_refl' _) hscaled
  exact lt_of_le_of_lt hceiling
    finePacketComponentChildExcessCeiling_anchor_lt_nine

/-! ## 3. Shape times child-resolved effective ratio -/

def finePacketComponentShapeChildWeightedEntropyRatio
    (rate : Q') : Q' :=
  Q'.ofNat 625 * (qpow rate 2 * Q'.ofNat 9)

theorem finePacketComponentShapeChildWeightedEntropyRatio_anchor_eqv :
    finePacketComponentShapeChildWeightedEntropyRatio anchorCoupling ≈
      Q'.mkPos 9 256 (by decide) := by
  unfold finePacketComponentShapeChildWeightedEntropyRatio
    anchorCoupling qpow
  decide

theorem finePacketComponentShapeChildWeightedEntropyRatio_anchor_lt_one :
    finePacketComponentShapeChildWeightedEntropyRatio anchorCoupling <
      (1 : Q') := by
  have hle := Q'.le_of_eqv
    finePacketComponentShapeChildWeightedEntropyRatio_anchor_eqv
  exact lt_of_le_of_lt hle (by decide)

theorem finePacketComponentShapeChildWeightedEntropyRatio_lt_one
    {rate : Q'} (hrate0 : (0 : Q') ≤ rate)
    (hrateAnchor : rate ≤ anchorCoupling) :
    finePacketComponentShapeChildWeightedEntropyRatio rate <
      (1 : Q') := by
  have hpow : qpow rate 2 ≤ qpow anchorCoupling 2 :=
    qpow_mono hrate0 hrateAnchor 2
  have hnine0 : (0 : Q') ≤ Q'.ofNat 9 := zero_le_ofNat 9
  have hinner := Q'.mul_le_mul_of_nonneg_right _ _ _ hpow hnine0
  have hbase0 : (0 : Q') ≤ Q'.ofNat 625 := zero_le_ofNat 625
  have hratio : finePacketComponentShapeChildWeightedEntropyRatio rate ≤
      finePacketComponentShapeChildWeightedEntropyRatio anchorCoupling := by
    unfold finePacketComponentShapeChildWeightedEntropyRatio
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hinner hbase0
  exact lt_of_le_of_lt hratio
    finePacketComponentShapeChildWeightedEntropyRatio_anchor_lt_one

/-! ## 4. Axiom audit -/

#print axioms finePacketComponentNonminimalChildCodes_length
#print axioms finePacketComponentChildExcessWeight
#print axioms finePacketComponentChildExcessMass
#print axioms finePacketComponentChildExcessCeiling
#print axioms finePacketComponentChildExcessMass_le_ceiling
#print axioms finePacketComponentChildExcessCeiling_anchor_lt_nine
#print axioms finePacketComponentChildExcessCeiling_lt_nine
#print axioms finePacketComponentShapeChildWeightedEntropyRatio
#print axioms finePacketComponentShapeChildWeightedEntropyRatio_anchor_eqv
#print axioms finePacketComponentShapeChildWeightedEntropyRatio_lt_one

end YMGap.Continuum.Z4DyadicBinaryConnectedComponentChildWeightedEntropy
