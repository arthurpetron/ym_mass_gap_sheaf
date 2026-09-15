/-
# Quantitative ORIGINAL reflected-numerator reconstruction by channel squares

Each retained packet is the finite sum over its actual original Gram tree,
using the original bulk-limiting channel amplitudes. These sums converge to
the pre-existing complete reflected numerator limit with two computed
thresholds. Vanishing of all actual finite-packet leaf coefficients forces
the original reflected numerator to vanish, and hence the SAME normalized
OS form and embedded original completed state to vanish.

This is an original finite-volume quadratic-form reconstruction, not a
Hilbert-space resolution or transfer range construction. It does not prove
the reverse leaf-vanishing implication, construct quantitative normalized
sum approximants, or pass to growing volumes. Time translation, full-space
zero-time continuity, physical scaling and continuum/Clay remain open.
-/

import YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit

namespace YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal
open YMGap.Continuum.BF4ExactSlabMixedInterfacePin
open YMGap.Continuum.BF4ExactSlabCrossingPacketBulkLimit
open YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.ReflectedSquareTreeRetainedChannel
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private theorem half_chain (a b c epsilon : Q')
    (hab : a ≤ b + HalfPow.half*epsilon) (hbc : b ≤ c + HalfPow.half*epsilon) :
    a ≤ c + epsilon :=
  Q'.le_trans' _ _ _ hab (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hbc)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves epsilon)))))

/-- The computed precision for the exact packet-to-finite-sum identity. -/
def packetEnergyApproxCutoff (b v : Q') (hb0 : (0 : Q') < b) (hb1 : b < (1 : Q'))
    (hv : (0 : Q') ≤ v) (N : Nat) {half : Nat} (e : PlaquetteExpression half) (epsilon : Q') : Nat :=
  max ((packetCauchy b v hb0 hb1 N e).M (HalfPow.half*epsilon))
    (energyApproxCutoff b hb0 half (lower e) (interfaceExpansion hv N half).tree (HalfPow.half*epsilon))

theorem packet_energy_approx_close (b v : Q') (hb0 : (0 : Q') < b) (hb1 : b < (1 : Q'))
    (hv : (0 : Q') ≤ v) (N : Nat) {half : Nat} (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : packetEnergyApproxCutoff b v hb0 hb1 hv N e epsilon ≤ n) :
    (packetLimit b v hb0 hb1 N e).approx n ≤
      (energyLimit b hb0 hb1 half (lower e) (interfaceExpansion hv N half).tree).approx n + epsilon ∧
    (energyLimit b hb0 hb1 half (lower e) (interfaceExpansion hv N half).tree).approx n ≤
      (packetLimit b v hb0 hb1 N e).approx n + epsilon := by
  have hp := mixed_approx_close b v hb0 hb1 N e (HalfPow.half*epsilon)
    (ExpNeg.half_mul_pos epsilon he) n n (Nat.le_trans (Nat.le_max_left _ _) hn) (Nat.le_trans (Nat.le_max_left _ _) hn)
  have hs := energy_approx_close b hb0 hb1 half (lower e) (interfaceExpansion hv N half).tree
    (interfaceExpansion hv N half).weightsNonnegative (HalfPow.half*epsilon)
    (ExpNeg.half_mul_pos epsilon he) n n (Nat.le_trans (Nat.le_max_right _ _) hn) (Nat.le_trans (Nat.le_max_right _ _) hn)
  have hpin := mixed_energy_pin b v hv n N e
  exact ⟨half_chain _ _ _ epsilon hp.2 (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin) hs.1),
    half_chain _ _ _ epsilon
      (Q'.le_trans' _ _ _ hs.2 (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv hpin))) hp.1⟩

theorem energyLimit_nonnegative (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (p : RatPoly) : (t : SquareTree) → t.Nonnegative →
    ∀ n, (0 : Q') ≤ (energyLimit w hw0 hw1 half p t).approx n
  | .zero, _, _ => by change (0 : Q') ≤ 0; decide
  | .term _ _, hv, _ => Q'.mul_nonneg _ _ hv (SumOfSquares.q_mul_self_nonneg _)
  | .add s t, h, n => Q'.zero_le_add _ _
      (energyLimit_nonnegative w hw0 hw1 half p s h.1 n) (energyLimit_nonnegative w hw0 hw1 half p t h.2 n)

/-- Every actual leaf is tested, including multiplicities in the finite tree. -/
theorem energyLimit_zero_of_coefficients_zero (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (p : RatPoly) : (t : SquareTree) →
    (∀ l : Leaf t, CReal.Equiv (coefficientLimit w hw0 hw1 half (polyMul p l.channel)) (CReal.ofQ' 0)) →
    CReal.Equiv (energyLimit w hw0 hw1 half p t) (CReal.ofQ' 0)
  | .zero, _ => CReal.Equiv.refl _
  | .term v q, h => by
      have hz := h (.here v q)
      have hs := Pivot2.mul_congr (CReal.Equiv.refl (CReal.ofQ' v)) (Pivot2.mul_congr hz hz)
      exact hs.trans (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (QPoly.q_mul_zero 0)) (QPoly.q_mul_zero v)))
  | .add s t, h =>
      (Pivot2.add_congr (energyLimit_zero_of_coefficients_zero w hw0 hw1 half p s (fun l => h (.left l)))
        (energyLimit_zero_of_coefficients_zero w hw0 hw1 half p t (fun l => h (.right l)))).trans
          (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_of_eq (Q'.zero_add' 0)))

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat} (e : PlaquetteExpression half)

local notation "actualTree" N => BF4ExactSlabLocalSquareExpansion.LocalSquareExpansion.tree
  (interfaceExpansion (Q'.le_of_lt hw0) N half)
local notation "originalLimit" => numeratorLimit w hw0 hw1
  (List.length (boundaryCompleteSlabLinks (centralExtent half))) (centralExtent half)
  (slabPhysicalFaceEdges (centralExtent half)) (reflectedInsertion e)

/-- No unspecified basis: this is the actual interface expansion's finite sum. -/
def channelPacket (N : Nat) : CReal := energyLimit w hw0 hw1 half (lower e) (actualTree N)

def channelPacketCauchy (N : Nat) : CReal.QCauchy (channelPacket w hw0 hw1 e N).approx :=
  energyLimitCauchy w hw0 hw1 half (lower e) (actualTree N)

theorem channelPacket_nonnegative (N : Nat) : CReal.leEv (CReal.ofQ' 0) (channelPacket w hw0 hw1 e N) :=
  CReal.leEv_ofQ'_of_approx_ge (energyLimit_nonnegative w hw0 hw1 half (lower e) (actualTree N)
    (interfaceExpansion (Q'.le_of_lt hw0) N half).weightsNonnegative)

def channelCutoff (epsilon : Q') : Nat := reconstructionCutoff w e (HalfPow.half*epsilon)

def channelApproxCutoff (N : Nat) (epsilon : Q') : Nat :=
  max (reconstructionApproxCutoff w e N (HalfPow.half*epsilon))
    (packetEnergyApproxCutoff w w hw0 hw1 (Q'.le_of_lt hw0) N e (HalfPow.half*epsilon))

/-- Quantitative reconstruction of the ORIGINAL full reflected numerator,
after all bulk cutoffs have already been removed from every channel. -/
theorem channelPacket_original_approx_close (epsilon : Q') (he : (0 : Q') < epsilon) (N n : Nat)
    (hN : channelCutoff w e epsilon ≤ N) (hn : channelApproxCutoff w hw0 hw1 e N epsilon ≤ n) :
    (channelPacket w hw0 hw1 e N).approx n ≤ (originalLimit).approx n + epsilon ∧
    (originalLimit).approx n ≤ (channelPacket w hw0 hw1 e N).approx n + epsilon := by
  have ho := packetLimit_original_approx_close w hw0 hw1 e (HalfPow.half*epsilon)
    (ExpNeg.half_mul_pos epsilon he) N n hN (Nat.le_trans (Nat.le_max_left _ _) hn)
  have hc := packet_energy_approx_close w w hw0 hw1 (Q'.le_of_lt hw0) N e (HalfPow.half*epsilon)
    (ExpNeg.half_mul_pos epsilon he) n (Nat.le_trans (Nat.le_max_right _ _) hn)
  exact ⟨half_chain _ _ _ epsilon hc.2 ho.1, half_chain _ _ _ epsilon ho.2 hc.1⟩

theorem channelPacket_converges : CReal.ConvergesTo (channelPacket w hw0 hw1 e) originalLimit :=
  fun epsilon he => ⟨channelCutoff w e epsilon, fun N hN =>
    ⟨channelApproxCutoff w hw0 hw1 e N epsilon, fun n hn =>
      channelPacket_original_approx_close w hw0 hw1 e epsilon he N n hN hn⟩⟩

def channelReconstructionCertificate (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' N₀ : Nat, Σ' M : Nat → Nat, ∀ N n : Nat, N₀ ≤ N → M N ≤ n →
      ((channelPacket w hw0 hw1 e N).approx n ≤ (originalLimit).approx n + epsilon ∧
       (originalLimit).approx n ≤ (channelPacket w hw0 hw1 e N).approx n + epsilon) :=
  ⟨channelCutoff w e epsilon, fun N => channelApproxCutoff w hw0 hw1 e N epsilon,
    fun N n hN hn => channelPacket_original_approx_close w hw0 hw1 e epsilon he N n hN hn⟩

/-- A proved implication about actual original coefficients, NOT an
assumption of channel completeness or a claim about the transfer kernel. -/
theorem original_null_of_all_channel_coefficients_zero
    (hz : ∀ N : Nat, ∀ l : Leaf (actualTree N),
      CReal.Equiv (coefficientLimit w hw0 hw1 half (polyMul (lower e) l.channel)) (CReal.ofQ' 0)) :
    CReal.Equiv originalLimit (CReal.ofQ' 0) :=
  CReal.Equiv_of_limit_of_equal
    (fun N => energyLimit_zero_of_coefficients_zero w hw0 hw1 half (lower e) (actualTree N) (hz N))
    (channelPacket_converges w hw0 hw1 e) (CReal.convergesTo_const (CReal.ofQ' 0))

/-- Normalize only by the already constructed ORIGINAL action reciprocal. -/
theorem form_null_of_all_channel_coefficients_zero
    (hz : ∀ N : Nat, ∀ l : Leaf (actualTree N),
      CReal.Equiv (coefficientLimit w hw0 hw1 half (polyMul (lower e) l.channel)) (CReal.ofQ' 0)) :
    CReal.Equiv (form w hw0 hw1 e e) (CReal.ofQ' 0) :=
  (expectation_reflection_eq_upper w e e hw0 hw1).symm.trans
    ((Pivot2.mul_congr_left (B := actionReciprocal w hw0 hw1 half)
      (original_null_of_all_channel_coefficients_zero w hw0 hw1 e hz)).trans
        (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_zero_mul
          ((actionReciprocal w hw0 hw1 half).approx n))))

/-- A conclusion in the pre-existing ORIGINAL completed carrier, for an
embedded dense expression. It asserts nothing about the transfer kernel. -/
theorem embedded_zero_of_all_channel_coefficients_zero
    (hz : ∀ N : Nat, ∀ l : Leaf (actualTree N),
      CReal.Equiv (coefficientLimit w hw0 hw1 half (polyMul (lower e) l.channel)) (CReal.ofQ' 0)) :
    embedExpression w hw0 hw1 e = completedZero w hw0 hw1 half :=
  (embedExpression_eq_iff w hw0 hw1 e (zeroExpression half)).mpr
    ((null_zero_iff w hw0 hw1 e).mpr
      (Quotient.sound (form_null_of_all_channel_coefficients_zero w hw0 hw1 e hz)))

end YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction

#print axioms YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction.packetEnergyApproxCutoff
#print axioms YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction.packet_energy_approx_close
#print axioms YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction.energyLimit_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction.energyLimit_zero_of_coefficients_zero
#print axioms YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction.channelPacket
#print axioms YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction.channelPacketCauchy
#print axioms YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction.channelPacket_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction.channelCutoff
#print axioms YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction.channelApproxCutoff
#print axioms YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction.channelPacket_original_approx_close
#print axioms YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction.channelPacket_converges
#print axioms YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction.channelReconstructionCertificate
#print axioms YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction.original_null_of_all_channel_coefficients_zero
#print axioms YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction.form_null_of_all_channel_coefficients_zero
#print axioms YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction.embedded_zero_of_all_channel_coefficients_zero
