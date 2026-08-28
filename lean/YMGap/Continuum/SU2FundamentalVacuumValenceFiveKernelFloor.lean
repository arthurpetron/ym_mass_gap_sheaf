/-
# A sharp floor for the four-fundamental valence-five kernel

The corrected-slab switching pivot has ambient degree five: its first four
external doubled-spin labels are fundamental and its final label is vacuum.
The complete valence-five recoupling is a composition of two Schur blocks.
For external word `(1,1,1,1,0)`, the first block is the genuine fundamental
two-channel block, while the second block has a singleton fixed-output fiber.

Selecting the middle state canonically from the final target therefore gives
one summand at least `1/4`; all other summands are nonnegative.  Hence every
entry of the complete production valence-five matrix is at least `1/4`.

Constructive contract: explicit proof-carrying SU(2) channels, exact finite
sums, and rational order only; no choice principle, unchecked existence
claim, or unbounded heartbeat option.
-/

import YMGap.Continuum.SU2FundamentalPhysicalSchurKernelFloor
import YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel

namespace YMGap.Continuum.SU2FundamentalVacuumValenceFiveKernelFloor

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelComposition
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SU2CanonicalHigherValenceFusionChainBridge
open YMGap.Continuum.SU2CanonicalValenceFourChannelBridge
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
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The output-zero second block is deterministic -/

private theorem outputZeroFixedRight_unique (m : Nat)
    (left right : FixedRightCGChannel 1 m 1 0) : left = right := by
  have hleftP := Nat.le_min.mp left.p_le
  have hrightP := Nat.le_min.mp right.p_le
  have hleftR := Nat.le_min.mp left.r_le
  have hrightR := Nat.le_min.mp right.r_le
  have hleftDegree := left.degree_eq
  have hrightDegree := right.degree_eq
  have hp : left.p = right.p := by
    unfold FixedRightCGChannel.intermediate at *
    omega
  exact fixedRightChannel_eq_of_p_eq left right hp

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

private theorem outputZeroFixedRightChannels_eq_singleton (m : Nat)
    (target : FixedRightCGChannel 1 m 1 0) :
    fixedRightChannels 1 m 1 0 = [target] :=
  singleton_of_nodup_of_mem_of_unique _ target
    (fixedRightChannels_nodup 1 m 1 0)
    (fixedRightChannels_complete target)
    (fun entry => outputZeroFixedRight_unique m entry target)

theorem outputZero_physicalSchurKernel_eqv_one (m : Nat)
    (source : FixedLeftCGChannel 1 m 1 0)
    (target : FixedRightCGChannel 1 m 1 0) :
    physicalSchurRecouplingKernelAt source target ≈ 1 := by
  have h := physicalSchurRecoupling_list_row_normalized source
  rw [show physicalSchurRightTargets source =
      fixedRightChannels 1 m 1 0 by rfl,
    outputZeroFixedRightChannels_eq_singleton m target] at h
  simpa only [listQSum, Q'.add_zero'] using h

/-! ## 2. A canonical contributing middle state -/

private def outputZeroLeftOfTarget
    (target : ValenceFiveRightCarrier 1 1 1 1 0) :
    FixedLeftCGChannel 1 target.m 1 0 :=
  fixedLeftChannelOfFusion 1 target.m 1 0 1
    (by
      rw [← fusionOK_symm_bt]
      exact target.inner.fusionOK)
    (by decide)

private theorem source_y_eq_one
    (source : ValenceFiveLeftCarrier 1 1 1 1 0) : source.y = 1 := by
  have horder := Nat.le_min.mp source.suffix.order_le
  have houtput := source.suffix.output_eq
  omega

private theorem selectedMiddle_y_eq_one
    (target : ValenceFiveRightCarrier 1 1 1 1 0) :
    (middleOfInnerLeft target.inner
      (outputZeroLeftOfTarget target)).y = 1 := by
  exact fixedLeftChannelOfFusion_intermediate
    1 target.m 1 0 1
      (by
        rw [← fusionOK_symm_bt]
        exact target.inner.fusionOK)
      (by decide)

private def castFixedRightOutput {a b c y z : Nat} (h : y = z)
    (channel : FixedRightCGChannel a b c y) :
    FixedRightCGChannel a b c z := h ▸ channel

private theorem selectedFirstKernel_oneQuarter_le
    (source : ValenceFiveLeftCarrier 1 1 1 1 0)
    (target : ValenceFiveRightCarrier 1 1 1 1 0) :
    oneQuarter ≤ valenceFiveFirstKernelAt source
      (middleOfInnerLeft target.inner (outputZeroLeftOfTarget target)) := by
  rcases source with ⟨sourceY, sourceFirst, sourceSuffix⟩
  have hsourceY : sourceY = 1 := by
    have horder := Nat.le_min.mp sourceSuffix.order_le
    have houtput := sourceSuffix.output_eq
    omega
  subst sourceY
  let middle := middleOfInnerLeft target.inner (outputZeroLeftOfTarget target)
  have hmiddle : middle.y = 1 := selectedMiddle_y_eq_one target
  have halign : 1 = middle.y := hmiddle.symm
  unfold valenceFiveFirstKernelAt
  rw [dif_pos halign]
  unfold valenceFiveFirstBlockKernelAt
  have hfloor := fundamental_physicalSchurKernel_oneQuarter_le
    sourceFirst (castFixedRightOutput hmiddle middle.first)
  simpa only [castFixedRightOutput] using hfloor

private theorem selectedSecondKernel_eqv_one
    (target : ValenceFiveRightCarrier 1 1 1 1 0) :
    valenceFiveSecondKernelAt
        (middleOfInnerLeft target.inner (outputZeroLeftOfTarget target))
        target ≈ 1 :=
  Q'.eqv_trans _ _ _
    (valenceFiveSecondKernelAt_middleOfInnerLeft target
      (outputZeroLeftOfTarget target))
    (outputZero_physicalSchurKernel_eqv_one target.m
      (outputZeroLeftOfTarget target) target.second)

/-! ## 3. Retain the selected summand in the completed kernel -/

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

theorem fundamentalVacuumValenceFiveKernel_oneQuarter_le
    (source : ValenceFiveLeftCarrier 1 1 1 1 0)
    (target : ValenceFiveRightCarrier 1 1 1 1 0) :
    oneQuarter ≤
      (valenceFiveBistochasticKernel 1 1 1 1 0).weight source target := by
  let middle := middleOfInnerLeft target.inner (outputZeroLeftOfTarget target)
  let first := valenceFiveFirstKernelAt source middle
  let second := valenceFiveSecondKernelAt middle target
  have hfirst : oneQuarter ≤ first :=
    selectedFirstKernel_oneQuarter_le source target
  have hfirstNonnegative : (0 : Q') ≤ first :=
    Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ oneQuarter) hfirst
  have hsecondEqv : second ≈ 1 := selectedSecondKernel_eqv_one target
  have hsecond : (1 : Q') ≤ second := Q'.ge_of_eqv hsecondEqv
  have hselected : oneQuarter ≤ first * second :=
    Q'.le_trans' _ first _ hfirst
      (Q'.le_trans' _ (first * 1) _
        (Q'.ge_of_eqv (Q'.mul_one_eqv first))
        (Q'.mul_le_mul_of_nonneg_left 1 second first hsecond
          hfirstNonnegative))
  have hmember : middle ∈ valenceFiveMiddleCarriers 1 1 1 1 0 :=
    valenceFiveMiddleCarriers_complete middle
  change oneQuarter ≤ listQSum
    (fun item => valenceFiveFirstKernelAt source item *
      valenceFiveSecondKernelAt item target)
    (valenceFiveMiddleCarriers 1 1 1 1 0)
  exact Q'.le_trans' _ (first * second) _ hselected
    (listQSum_member_le_nonnegative
      (fun item => valenceFiveFirstKernelAt source item *
        valenceFiveSecondKernelAt item target)
      (fun item => Q'.mul_nonneg _ _
        (valenceFiveFirstKernelAt_nonnegative source item)
        (valenceFiveSecondKernelAt_nonnegative item target))
      (items := valenceFiveMiddleCarriers 1 1 1 1 0) hmember)

theorem fundamentalVacuumValenceFiveKernel_pos
    (source : ValenceFiveLeftCarrier 1 1 1 1 0)
    (target : ValenceFiveRightCarrier 1 1 1 1 0) :
    (0 : Q') <
      (valenceFiveBistochasticKernel 1 1 1 1 0).weight source target :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < oneQuarter)
    (fundamentalVacuumValenceFiveKernel_oneQuarter_le source target)

end YMGap.Continuum.SU2FundamentalVacuumValenceFiveKernelFloor

#print axioms YMGap.Continuum.SU2FundamentalVacuumValenceFiveKernelFloor.outputZero_physicalSchurKernel_eqv_one
#print axioms YMGap.Continuum.SU2FundamentalVacuumValenceFiveKernelFloor.fundamentalVacuumValenceFiveKernel_oneQuarter_le
#print axioms YMGap.Continuum.SU2FundamentalVacuumValenceFiveKernelFloor.fundamentalVacuumValenceFiveKernel_pos
