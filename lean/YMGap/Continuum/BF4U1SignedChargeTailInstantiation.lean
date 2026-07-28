/-
# Instantiating the BF4 U(1) one-charge tail

The signed-charge heat tail is a one-coordinate analytic estimate, while the
BF4 cutoff bridge consumes a pointwise `OneChargeTail` and a carrier-amplified
modulus.  This module joins those two layers at every fixed corrected-slab
datum whose heat coupling lies strictly between zero and one.

The pointwise estimate first lowers an omitted charge to the first omitted
charge, then bounds that coefficient by the first geometric increment and
finally by the closed signed-charge tail.  For the modulus, the tolerance is
divided by the positive finite carrier cardinality before applying the
explicit signed-charge cutoff.
-/

import YMGap.Continuum.BF4U1ExponentGramCutoffTailBridge
import YMGap.Continuum.U1SignedChargeHeatTail

namespace YMGap.Continuum.BF4U1SignedChargeTailInstantiation

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.AbelianFusionCLT
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator
open YMGap.Continuum.BF4U1ExponentGramCutoffTailBridge
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.U1SignedChargeHeatTail

local infix:50 " ≈ " => Q'.eqv

private theorem ofNat_pos_of_pos {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  cases n with
  | zero => omega
  | succ n => exact Q'.ofNat_succ_pos n

/-- The genuine finite BF4 U(1) carrier contains the vacuum state, so its
cardinality is a positive rational scale. -/
theorem u1StateCarrierScale_pos (D : U1SlabData) :
    (0 : Q') < Q'.ofNat D.states.length :=
  ofNat_pos_of_pos
    (List.length_pos_of_mem D.zero_mem_states)

/-- A coefficient whose charge lies beyond `cutoff` is bounded by the first
omitted coefficient. -/
theorem abelCoeff_le_first_omitted
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {cutoff charge : Nat} (hout : cutoff < charge) :
    abelCoeff w charge ≤ abelCoeff w (cutoff + 1) := by
  have hsucc : cutoff + 1 ≤ charge := by omega
  have hsquare :
      (cutoff + 1) * (cutoff + 1) ≤ charge * charge :=
    Nat.mul_le_mul hsucc hsucc
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (abelCoeff_eqv_pow w charge)) ?_
  refine Q'.le_trans' _ _ _
    (pow_base_antitone
      (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
      hsquare) ?_
  exact Q'.ge_of_eqv
    (abelCoeff_eqv_pow w (cutoff + 1))

/-- The first omitted charge is below the first term of the closed geometric
majorant. -/
theorem abelCoeff_first_omitted_le_geo
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff : Nat) :
    abelCoeff w (cutoff + 1) ≤
      geoIncrBase (w + w) w cutoff := by
  have hcoeff :=
    abelCoeff_succ_le_geometric hw0 hw1 cutoff
  have hwadd :
      w ≤ w + w :=
    Q'.add_le_self_of_nonneg w w (Q'.le_of_lt hw0)
  have hscale :
      w * w ^ cutoff ≤ (w + w) * w ^ cutoff :=
    Q'.mul_le_mul_of_nonneg_right
      _ _ _ hwadd
      (Q'.pow_nonneg w (Q'.le_of_lt hw0) cutoff)
  exact Q'.le_trans' _ _ _ hcoeff hscale

/-- One geometric increment is bounded by the corresponding closed tail. -/
theorem signedChargeGeoIncr_le_closedTail
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff : Nat) :
    geoIncrBase (w + w) w cutoff ≤
      signedChargeClosedTail w cutoff := by
  have hseries :=
    geoTailBase_series_le
      (Q'.le_of_lt (Q'.add_pos hw0 hw0))
      hw0 hw1 cutoff 1
  change
    (0 : Q') +
        geoIncrBase (w + w) w (cutoff + 0) ≤
      signedChargeClosedTail w cutoff at hseries
  simpa only [Nat.add_zero, Q'.zero_add'] using hseries

/-- The closed signed-charge tail is the concrete pointwise analytic datum
consumed by the finite BF4 cutoff bridge. -/
def signedChargeOneChargeTail
    (D : U1SlabData)
    (hw0 : (0 : Q') < D.coupling)
    (hw1 : D.coupling < (1 : Q')) :
    OneChargeTail D where
  tail := signedChargeClosedTail D.coupling
  tail_nonnegative :=
    signedChargeClosedTail_nonnegative hw0
  charge_bound := by
    intro cutoff charge hout
    exact Q'.le_trans' _ _ _
      (abelCoeff_le_first_omitted hw0 hw1 hout)
      (Q'.le_trans' _ _ _
        (abelCoeff_first_omitted_le_geo hw0 hw1 cutoff)
        (signedChargeGeoIncr_le_closedTail hw0 hw1 cutoff))

/-- Carrier-rescaled tolerance used by the explicit signed-charge cutoff. -/
def signedChargeCarrierTolerance
    (D : U1SlabData) (ε : Q') : Q' :=
  HKConv.divPos ε (Q'.ofNat D.states.length)

/-- Explicit cutoff after paying the exact finite BF4 carrier amplification. -/
def signedChargeCarrierCutoff
    (D : U1SlabData) (ε : Q') : Nat :=
  signedChargePairCutoff D.coupling
    (signedChargeCarrierTolerance D ε)

theorem signedChargeCarrierTolerance_pos
    (D : U1SlabData) {ε : Q'} (hε : (0 : Q') < ε) :
    (0 : Q') < signedChargeCarrierTolerance D ε :=
  HKConv.divPos_pos
    (CReal.num_pos_of_pos hε)

theorem stateScale_mul_carrierTolerance_eqv
    (D : U1SlabData) (ε : Q') :
    Q'.ofNat D.states.length *
        signedChargeCarrierTolerance D ε ≈
      ε := by
  unfold signedChargeCarrierTolerance
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv
      (Q'.ofNat D.states.length)
      (HKConv.divPos ε
        (Q'.ofNat D.states.length))) ?_
  exact HKConv.divPos_mul_eqv
    (CReal.num_pos_of_pos
      (u1StateCarrierScale_pos D))

/-- Fully concrete fixed-slab tail modulus.  Its cutoff is the existing
signed-charge power cutoff evaluated at `ε / |states|`; therefore the exact
carrier factor in the BF4 tail bridge is paid before the cutoff is chosen. -/
def signedChargeOneChargeTailModulus
    (D : U1SlabData)
    (hw0 : (0 : Q') < D.coupling)
    (hw1 : D.coupling < (1 : Q')) :
    OneChargeTailModulus D where
  toOneChargeTail :=
    signedChargeOneChargeTail D hw0 hw1
  cutoff :=
    signedChargeCarrierCutoff D
  scaled_tail := by
    intro ε hε M hM
    have htail :
        signedChargeClosedTail D.coupling M ≤
          signedChargeCarrierTolerance D ε :=
      signedChargeClosedTail_le_of_cutoff
        hw0 hw1
        (signedChargeCarrierTolerance_pos D hε)
        M hM
    have hscaled :
        Q'.ofNat D.states.length *
            signedChargeClosedTail D.coupling M ≤
          Q'.ofNat D.states.length *
            signedChargeCarrierTolerance D ε :=
      Q'.mul_le_mul_of_nonneg_left
        _ _ _
        htail
        (Q'.le_of_lt
          (u1StateCarrierScale_pos D))
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv
        (stateScale_mul_carrierTolerance_eqv
          D ε))

/-- The generic genuine-slab exponent-Gram estimate with every analytic tail
field discharged by the explicit signed-charge construction above. -/
theorem u1ExponentGramDiagonalSignedChargeCutoff_modulus
    (D : U1SlabData)
    (hw0 : (0 : Q') < D.coupling)
    (hw1 : D.coupling < (1 : Q'))
    (exponent : Nat)
    (ε : Q') (hε : (0 : Q') < ε)
    (M : Nat)
    (hM : signedChargeCarrierCutoff D ε ≤ M) :
    u1ExponentGramEntry
          D.half D.states D.normalizedMass
          { leftExponent := exponent,
            rightExponent := exponent } +
        -u1ExponentGramDiagonalChargeCutoff
          D exponent M ≤
      ε :=
  u1ExponentGramDiagonalChargeCutoff_modulus
    D (Q'.le_of_lt hw1)
    (signedChargeOneChargeTailModulus
      D hw0 hw1)
    exponent ε hε M hM

/-- The same explicit tail modulus after the already-proved deterministic
BF4 block and fine-pullback identity. -/
theorem u1BlockedExponentGramDiagonalSignedChargeCutoff_modulus
    (G : CutoffOneGeometry)
    (g : Q') (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff exponent : Nat)
    (ε : Q') (hε : (0 : Q') < ε)
    (M : Nat)
    (hM :
      signedChargeCarrierCutoff
          (fineU1Data G g (Q'.le_of_lt hg0)
            fineChargeCutoff) ε ≤
        M) :
    u1BlockedExponentGramEntry
          G g (Q'.le_of_lt hg0)
          candidate hcandidate fineChargeCutoff
          { leftExponent := exponent,
            rightExponent := exponent } +
        -u1BlockedExponentGramDiagonalChargeCutoff
          G g (Q'.le_of_lt hg0)
          fineChargeCutoff exponent M ≤
      ε :=
  u1BlockedExponentGramDiagonalChargeCutoff_modulus
    G g (Q'.le_of_lt hg0) (Q'.le_of_lt hg1)
    candidate hcandidate fineChargeCutoff
    (signedChargeOneChargeTailModulus
      (fineU1Data G g (Q'.le_of_lt hg0)
        fineChargeCutoff)
      hg0 hg1)
    exponent ε hε M hM

#print axioms abelCoeff_le_first_omitted
#print axioms signedChargeGeoIncr_le_closedTail
#print axioms signedChargeOneChargeTail
#print axioms signedChargeCarrierTolerance_pos
#print axioms signedChargeOneChargeTailModulus
#print axioms u1ExponentGramDiagonalSignedChargeCutoff_modulus
#print axioms u1BlockedExponentGramDiagonalSignedChargeCutoff_modulus

end YMGap.Continuum.BF4U1SignedChargeTailInstantiation
