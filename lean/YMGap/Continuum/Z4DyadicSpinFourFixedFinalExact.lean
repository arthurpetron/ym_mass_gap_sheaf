/-
# Exact fixed-final weight of the canonical spin-zero-through-four packets

The spin-four dyadic lift assigns to a coarse spin `s <= 4` a canonical
four-bit fine packet whose total spin is `s`.  This file proves that after
summing both internal pair channels while fixing the retained final spin to
`s`, the exact face weight is `coeffW w s`.

The reason is structural rather than tabular.  Each internal fusion channel
is at most the sum of its two packet entries.  Reaching the maximal final
spin, the sum of all four entries, forces both internal channels to attain
their maxima.  Thus the stretched channel is the unique surviving summand.

This is the facewise algebra needed to evaluate the simultaneous multi-face
endpoint lift at its complete closed coarse target.  It is not a statement
that arbitrary retained targets or arbitrary background insertions factor.

Constructive contract: finite exact-rational sums and SU(2) fusion bounds
only; no `Classical`, choice, `native_decide`, proof hole, noncomputable
declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicPairBubbleRetainedTargetSum
import YMGap.Continuum.Z4DyadicSpinFourXorAssembly
import YMGap.Continuum.Z4DyadicSlabCubePhysicalSummandBridge

namespace YMGap.Continuum.Z4DyadicSpinFourFixedFinalExact

set_option autoImplicit false
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualCutoffOneCoarseFaceDoor
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicPairBubbleRetainedTargetSum
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabCubePhysicalSummandBridge
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSlabTwoFaceCoupledConditionalKernel
open YMGap.Continuum.Z4DyadicSpinFourXorAssembly

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_zero_of_left_local
    {left right : Q'} (hleft : left ≈ 0) :
    left * right ≈ 0 :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right left 0 right hleft)
    (Q'.zero_mul_eqv right)

private theorem mul_eqv_zero_of_right_local
    {left right : Q'} (hright : right ≈ 0) :
    left * right ≈ 0 :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left left right 0 hright)
    (Q'.mul_zero_eqv left)

private theorem packetPairChannelRawWeight_eqv_zero_of_support_false_local
    (w : Q') (packet : FaceSpinPacket) (state : PairChannelState)
    (hsupport : packetPairChannelSupportedBool packet state = false) :
    packetPairChannelRawWeight w packet state ≈ 0 := by
  unfold packetPairChannelSupportedBool at hsupport
  cases hleft : fusionOK packet.spin0 packet.spin1 state.1.1 with
  | false =>
      have hind :
          fusionInd packet.spin0 packet.spin1 state.1.1 = (0 : Q') := by
        unfold fusionInd
        simp [hleft]
      unfold packetPairChannelRawWeight
      rw [hind]
      exact mul_eqv_zero_of_right_local
        (mul_eqv_zero_of_left_local (Q'.eqv_refl 0))
  | true =>
      cases hright : fusionOK packet.spin2 packet.spin3 state.1.2 with
      | false =>
          have hind :
              fusionInd packet.spin2 packet.spin3 state.1.2 = (0 : Q') := by
            unfold fusionInd
            simp [hright]
          unfold packetPairChannelRawWeight
          rw [hind]
          exact mul_eqv_zero_of_right_local
            (mul_eqv_zero_of_right_local
              (mul_eqv_zero_of_left_local (Q'.eqv_refl 0)))
      | true =>
          cases hcoarse : fusionOK state.1.1 state.1.2 state.2 with
          | false =>
              have hind :
                  fusionInd state.1.1 state.1.2 state.2 = (0 : Q') := by
                unfold fusionInd
                simp [hcoarse]
              unfold packetPairChannelRawWeight
              rw [hind]
              exact mul_eqv_zero_of_right_local
                (mul_eqv_zero_of_right_local
                  (mul_eqv_zero_of_right_local (Q'.eqv_refl 0)))
          | true => simp [hleft, hright, hcoarse] at hsupport

/-! ## 1. Uniqueness of the maximal final channel -/

/-- If a supported pair channel reaches the sum of all four packet spins,
both internal pair channels are forced to be their respective maximal sums. -/
theorem packetPairChannelSupportedBool_maximal_final_eq_stretched
    (packet : FaceSpinPacket) (state : PairChannelState)
    (hfinal : state.2 = faceSpinTotal packet)
    (hsupported : packetPairChannelSupportedBool packet state = true) :
    state = stretchedPairChannelState packet := by
  rcases packet with ⟨spin0, spin1, spin2, spin3⟩
  rcases state with ⟨⟨left, right⟩, final⟩
  simp only at hfinal ⊢
  unfold packetPairChannelSupportedBool at hsupported
  simp only [Bool.and_eq_true] at hsupported
  have hleft :=
    (fusionOK_eq_true_iff spin0 spin1 left).mp hsupported.1.1
  have hright :=
    (fusionOK_eq_true_iff spin2 spin3 right).mp hsupported.1.2
  have htop :=
    (fusionOK_eq_true_iff left right final).mp hsupported.2
  change final = spin0 + spin1 + spin2 + spin3 at hfinal
  have hleftLe : left ≤ spin0 + spin1 := hleft.2.1
  have hrightLe : right ≤ spin2 + spin3 := hright.2.1
  have htotalLe : spin0 + spin1 + spin2 + spin3 ≤ left + right := by
    rw [← hfinal]
    exact htop.2.1
  have hleftMax : left = spin0 + spin1 := by
    omega
  have hrightMax : right = spin2 + spin3 := by
    omega
  subst left
  subst right
  subst final
  unfold stretchedPairChannelState faceSpinTotal
  rfl

theorem packetPairChannelSupportedBool_eq_false_of_maximal_final_ne_stretched
    (packet : FaceSpinPacket) (state : PairChannelState)
    (hfinal : state.2 = faceSpinTotal packet)
    (hne : state ≠ stretchedPairChannelState packet) :
    packetPairChannelSupportedBool packet state = false := by
  cases hsupported : packetPairChannelSupportedBool packet state with
  | false => rfl
  | true =>
      exact False.elim
        (hne
          (packetPairChannelSupportedBool_maximal_final_eq_stretched
            packet state hfinal hsupported))

theorem packetPairChannelRawWeight_eqv_zero_of_maximal_final_ne_stretched
    (w : Q') (packet : FaceSpinPacket) (state : PairChannelState)
    (hfinal : state.2 = faceSpinTotal packet)
    (hne : state ≠ stretchedPairChannelState packet) :
    packetPairChannelRawWeight w packet state ≈ 0 :=
  packetPairChannelRawWeight_eqv_zero_of_support_false_local
    w packet state
    (packetPairChannelSupportedBool_eq_false_of_maximal_final_ne_stretched
      packet state hfinal hne)

/-! ## 2. Contract the complete cutoff-one channel sum -/

private theorem listQSum_zero_on_local
    {A : Type} (value : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → value item ≈ 0) →
      listQSum value items ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      change value head + listQSum value tail ≈ 0
      exact Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr'
          (hzero head List.mem_cons_self)
          (listQSum_zero_on_local value tail
            (fun item hmem =>
              hzero item (List.mem_cons_of_mem head hmem))))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem listQSum_eqv_single_of_mem_local
    {A : Type} [DecidableEq A] (value : A → Q') (selected : A) :
    ∀ (items : List A), items.Nodup → selected ∈ items →
      (∀ item, item ∈ items → item ≠ selected → value item ≈ 0) →
      listQSum value items ≈ value selected
  | [], _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | head :: tail, hnodup, hmem, hzero => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with heq | htail
      · subst head
        change value selected + listQSum value tail ≈ value selected
        have htailZero : listQSum value tail ≈ 0 := by
          apply listQSum_zero_on_local value tail
          intro item hitem
          have hitemNe : item ≠ selected := by
            intro heq
            subst item
            exact hparts.1 hitem
          exact hzero item
            (List.mem_cons_of_mem selected hitem) hitemNe
        exact Q'.eqv_trans _ (value selected + 0) _
          (Q'.add_eqv_congr_left _ _ _ htailZero)
          (Q'.eqv_of_eq (Q'.add_zero' _))
      · have hheadNe : head ≠ selected := by
          intro heq
          subst head
          exact hparts.1 htail
        change value head + listQSum value tail ≈ value selected
        exact Q'.eqv_trans _ (0 + value selected) _
          (Q'.add_eqv_congr'
            (hzero head List.mem_cons_self hheadNe)
            (listQSum_eqv_single_of_mem_local value selected tail
              hparts.2 htail
              (fun item hmem hne =>
                hzero item (List.mem_cons_of_mem head hmem) hne)))
          (Q'.eqv_of_eq (Q'.zero_add' _))

/-- At a maximal retained final spin, the complete cutoff-one internal
pair-channel sum reduces to the unique stretched channel. -/
theorem fixedFinalFaceRawWeight_maximal_eqv_stretched
    (w : Q') (packet : FaceSpinPacket)
    (hselected : stretchedPairChannelState packet ∈
      pairChannelStateSpace 1) :
    fixedFinalFaceRawWeight w packet (faceSpinTotal packet) ≈
      packetPairChannelRawWeight w packet
        (stretchedPairChannelState packet) := by
  unfold fixedFinalFaceRawWeight
  let value : PairChannelState → Q' := fun state =>
    if state.2 = faceSpinTotal packet then
      packetPairChannelRawWeight w packet state
    else 0
  refine Q'.eqv_trans _ (value (stretchedPairChannelState packet)) _ ?_ ?_
  · exact listQSum_eqv_single_of_mem_local value
      (stretchedPairChannelState packet) (pairChannelStateSpace 1)
      (pairChannelStateSpace_nodup 1) hselected (by
        intro state _ hne
        unfold value
        by_cases hfinal : state.2 = faceSpinTotal packet
        · rw [if_pos hfinal]
          exact
            packetPairChannelRawWeight_eqv_zero_of_maximal_final_ne_stretched
              w packet state hfinal hne
        · rw [if_neg hfinal]
          exact Q'.eqv_refl 0)
  · unfold value stretchedPairChannelState
    rw [if_pos rfl]
    exact Q'.eqv_refl _

theorem faceSpinTotal_spinFourPacket
    {spin : Nat} (hspin : spin ≤ 4) :
    faceSpinTotal (spinFourPacket spin) = spin := by
  simpa only [faceSpinTotal, faceSpinPacketTotal] using
    faceSpinPacketTotal_spinFourPacket hspin

theorem stretchedPairChannelState_spinFourPacket_mem
    {spin : Nat} (hspin : spin ≤ 4) :
    stretchedPairChannelState (spinFourPacket spin) ∈
      pairChannelStateSpace 1 := by
  have hcases : spin = 0 ∨ spin = 1 ∨ spin = 2 ∨
      spin = 3 ∨ spin = 4 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Exact heat-weight preservation on the canonical packet for every coarse
spin admitted by the spin-four endpoint lift. -/
theorem spinFourPacket_fixedFinalFaceRawWeight_eqv_coeffW
    (w : Q') {spin : Nat} (hspin : spin ≤ 4) :
    fixedFinalFaceRawWeight w (spinFourPacket spin) spin ≈
      coeffW w spin := by
  have htotal := faceSpinTotal_spinFourPacket hspin
  have hleftEq :
      fixedFinalFaceRawWeight w (spinFourPacket spin) spin =
        fixedFinalFaceRawWeight w (spinFourPacket spin)
          (faceSpinTotal (spinFourPacket spin)) :=
    congrArg (fixedFinalFaceRawWeight w (spinFourPacket spin)) htotal.symm
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_of_eq hleftEq)
    (Q'.eqv_trans _ _ _
      (fixedFinalFaceRawWeight_maximal_eqv_stretched
        w (spinFourPacket spin)
        (stretchedPairChannelState_spinFourPacket_mem hspin))
      (by
        simpa only [htotal] using
          (stretchedPairChannelRawWeight_eqv_coarseCoefficient
            w (spinFourPacket spin))))

#print axioms packetPairChannelSupportedBool_maximal_final_eq_stretched
#print axioms packetPairChannelSupportedBool_eq_false_of_maximal_final_ne_stretched
#print axioms packetPairChannelRawWeight_eqv_zero_of_maximal_final_ne_stretched
#print axioms fixedFinalFaceRawWeight_maximal_eqv_stretched
#print axioms faceSpinTotal_spinFourPacket
#print axioms stretchedPairChannelState_spinFourPacket_mem
#print axioms spinFourPacket_fixedFinalFaceRawWeight_eqv_coeffW

end YMGap.Continuum.Z4DyadicSpinFourFixedFinalExact
