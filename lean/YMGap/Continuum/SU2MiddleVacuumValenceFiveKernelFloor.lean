/-
# A sharp floor with the vacuum in the third valence-five slot

For the external word `(1,1,0,1,1)`, the first associator crosses a vacuum
third leg and is deterministic.  The second associator is the genuine
four-fundamental two-channel block.  Retaining the middle state determined by
the source therefore gives one summand at least `1/4`; all other summands are
nonnegative.  Hence every entry of the complete valence-five kernel has the
sharp `1/4` floor.

Constructive contract: proof-carrying SU(2) channels, exact finite sums, and
rational order only; no choice, `Classical`, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.SU2FundamentalPhysicalSchurKernelFloor
import YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel

namespace YMGap.Continuum.SU2MiddleVacuumValenceFiveKernelFloor

set_option autoImplicit false
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelComposition
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FundamentalPhysicalSchurKernelFloor
open YMGap.Continuum.SU2PhysicalSchurBistochasticKernel
open YMGap.Continuum.SU2PhysicalSchurRecouplingKernel
open YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport
open YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier
open YMGap.Continuum.SU2ValenceFiveFirstBistochasticBlock
open YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A vacuum third leg makes the first associator deterministic -/

private theorem middleVacuumFixedRight_unique (y : Nat)
    (left right : FixedRightCGChannel 1 1 0 y) : left = right := by
  apply fixedRightChannel_eq_of_p_eq
  have hleft := Nat.le_min.mp left.p_le
  have hright := Nat.le_min.mp right.p_le
  omega

private theorem singleton_of_nodup_of_mem_of_unique {A : Type}
    (items : List A) (item : A) (hnodup : items.Nodup)
    (hmem : item ∈ items) (hunique : ∀ entry, entry = item) :
    items = [item] := by
  cases items with
  | nil => exact False.elim (List.not_mem_nil hmem)
  | cons head tail =>
      have hhead := hunique head
      have htail : tail = [] := by
        cases tail with
        | nil => rfl
        | cons next rest =>
            have hparts := List.nodup_cons.mp hnodup
            have hnext := hunique next
            exact False.elim (hparts.1 (by
              rw [hnext, ← hhead]
              exact List.mem_cons_self))
      rw [hhead, htail]

private theorem middleVacuumFixedRightChannels_eq_singleton (y : Nat)
    (target : FixedRightCGChannel 1 1 0 y) :
    fixedRightChannels 1 1 0 y = [target] :=
  singleton_of_nodup_of_mem_of_unique _ target
    (fixedRightChannels_nodup 1 1 0 y)
    (fixedRightChannels_complete target)
    (fun entry => middleVacuumFixedRight_unique y entry target)

theorem middleVacuum_physicalSchurKernel_eqv_one (y : Nat)
    (source : FixedLeftCGChannel 1 1 0 y)
    (target : FixedRightCGChannel 1 1 0 y) :
    physicalSchurRecouplingKernelAt source target ≈ 1 := by
  have h := physicalSchurRecoupling_list_row_normalized source
  rw [show physicalSchurRightTargets source =
      fixedRightChannels 1 1 0 y by rfl,
    middleVacuumFixedRightChannels_eq_singleton y target] at h
  simpa only [listQSum, Q'.add_zero'] using h

/-! ## 2. Retain the source-determined middle state -/

private def middleVacuumRightOfSource
    (source : ValenceFiveLeftCarrier 1 1 0 1 1) :
    FixedRightCGChannel 1 1 0 source.y where
  p := 0
  p_le := by decide
  r := source.firstLeft.k
  r_le := by
    exact source.firstLeft.k_le
  degree_eq := by
    have hr : source.firstLeft.r = 0 := by
      have hbound := Nat.le_min.mp source.firstLeft.r_le
      omega
    have hdegree := source.firstLeft.degree_eq
    simp only [hr, Nat.mul_zero, Nat.sub_zero, Nat.add_zero] at hdegree
    omega

private def selectedMiddle
    (source : ValenceFiveLeftCarrier 1 1 0 1 1) :
    ValenceFiveMiddleCarrier 1 1 0 1 1 where
  y := source.y
  first := middleVacuumRightOfSource source
  suffix := source.suffix

private theorem selectedFirstKernel_eqv_one
    (source : ValenceFiveLeftCarrier 1 1 0 1 1) :
    valenceFiveFirstKernelAt source (selectedMiddle source) ≈ 1 := by
  unfold valenceFiveFirstKernelAt
  have halign : source.y = (selectedMiddle source).y := rfl
  rw [dif_pos halign]
  unfold valenceFiveFirstBlockKernelAt selectedMiddle
  exact middleVacuum_physicalSchurKernel_eqv_one source.y
    source.firstLeft (middleVacuumRightOfSource source)

private theorem middleVacuumTarget_m_eq_one
    (target : ValenceFiveRightCarrier 1 1 0 1 1) :
    target.m = 1 := by
  have horder := Nat.le_min.mp target.inner.order_le
  have houtput := target.inner.output_eq
  omega

private theorem selectedSecondKernel_oneQuarter_le
    (source : ValenceFiveLeftCarrier 1 1 0 1 1)
    (target : ValenceFiveRightCarrier 1 1 0 1 1) :
    oneQuarter ≤
      valenceFiveSecondKernelAt (selectedMiddle source) target := by
  cases target with
  | mk m inner second =>
      have hm : m = 1 := by
        have horder := Nat.le_min.mp inner.order_le
        have houtput := inner.output_eq
        omega
      subst m
      unfold valenceFiveSecondKernelAt
      have halign :
          (selectedMiddle source).first.intermediate = 1 := rfl
      rw [dif_pos halign]
      unfold valenceFiveSecondBlockKernelAt
      simpa only [selectedMiddle, middleVacuumRightOfSource,
          FixedRightCGChannel.intermediate] using
        (fundamental_physicalSchurKernel_oneQuarter_le
          (selectedMiddle source).secondLeft second)

/-! ## 3. Retain this positive summand in the complete kernel -/

private theorem listQSum_member_le_nonnegative {A : Type}
    (value : A → Q') (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {selected : A}, selected ∈ items →
      value selected ≤ listQSum value items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, selected, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_on value tail
            (fun item _ => hvalue item))
      · have ih := listQSum_member_le_nonnegative value hvalue tail htail
        have htailLe : listQSum value tail ≤
            value head + listQSum value tail := by
          have hadd := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hadd
        exact Q'.le_trans' _ _ _ ih htailLe

theorem middleVacuumValenceFiveKernel_oneQuarter_le
    (source : ValenceFiveLeftCarrier 1 1 0 1 1)
    (target : ValenceFiveRightCarrier 1 1 0 1 1) :
    oneQuarter ≤
      (valenceFiveBistochasticKernel 1 1 0 1 1).weight source target := by
  let middle := selectedMiddle source
  let first := valenceFiveFirstKernelAt source middle
  let second := valenceFiveSecondKernelAt middle target
  have hfirstEqv : first ≈ 1 := selectedFirstKernel_eqv_one source
  have honeLeFirst : (1 : Q') ≤ first := Q'.ge_of_eqv hfirstEqv
  have hsecond : oneQuarter ≤ second :=
    selectedSecondKernel_oneQuarter_le source target
  have hsecondNonnegative : (0 : Q') ≤ second :=
    Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ oneQuarter) hsecond
  have hselected : oneQuarter ≤ first * second :=
    Q'.le_trans' _ second _ hsecond
      (Q'.le_trans' _ (1 * second) _
        (Q'.ge_of_eqv (Q'.one_mul_eqv second))
        (Q'.mul_le_mul_of_nonneg_right 1 first second
          honeLeFirst hsecondNonnegative))
  have hmember : middle ∈ valenceFiveMiddleCarriers 1 1 0 1 1 :=
    valenceFiveMiddleCarriers_complete middle
  change oneQuarter ≤ listQSum
    (fun item => valenceFiveFirstKernelAt source item *
      valenceFiveSecondKernelAt item target)
    (valenceFiveMiddleCarriers 1 1 0 1 1)
  exact Q'.le_trans' _ (first * second) _ hselected
    (listQSum_member_le_nonnegative
      (fun item => valenceFiveFirstKernelAt source item *
        valenceFiveSecondKernelAt item target)
      (fun item => Q'.mul_nonneg _ _
        (valenceFiveFirstKernelAt_nonnegative source item)
        (valenceFiveSecondKernelAt_nonnegative item target))
      (items := valenceFiveMiddleCarriers 1 1 0 1 1) hmember)

theorem middleVacuumValenceFiveKernel_pos
    (source : ValenceFiveLeftCarrier 1 1 0 1 1)
    (target : ValenceFiveRightCarrier 1 1 0 1 1) :
    (0 : Q') <
      (valenceFiveBistochasticKernel 1 1 0 1 1).weight source target :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < oneQuarter)
    (middleVacuumValenceFiveKernel_oneQuarter_le source target)

#print axioms middleVacuum_physicalSchurKernel_eqv_one
#print axioms middleVacuumValenceFiveKernel_oneQuarter_le
#print axioms middleVacuumValenceFiveKernel_pos

end YMGap.Continuum.SU2MiddleVacuumValenceFiveKernelFloor
