/-
Track 11.7-fusion / R4j -- one-row compression of the heat-matched parity
frontier.

The heat-matched automaton was reduced to two infinite transition schemas:
an odd two-step row with factor `w^2`, and an even adjacent row with factor
`w`.  They are not independent.  Multiplying the adjacent rows centred at
`s+1` and `s+2` produces the odd row; the common positive middle states
cancel.  Consequently one adjacent strong-Turan family generates the entire
parity automaton.

This is a proof about the computation, not a scan of its cells.  The remaining
honest analytic input is the single all-row half-time Turan inequality on the
physical schedule.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2HalfTimeParityStrandCompiler

namespace YMGap.Continuum.P2HalfTimeStrongTuranCompiler

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionKernelStatement
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.P2BlockCompatibleHeadLinearCertificate
open YMGap.Continuum.P2BlockCompatibleParityTransitionCertificate
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.P2HalfTimeParityStrandCompiler
open YMGap.Continuum.P2RetunedFenceIntegralCertificate
open YMGap.Continuum.P2RetunedParityStrandCompiler
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One-row strong Turan datum -/

/-- The single adjacent strong-Turan row which generates both parity
transitions.  Its centre is `t`: the left and right states at `t-1` and `t`
are interlaced with the exact half-time factor `w`. -/
structure P2HalfTimeBoxStrongTuran (N : Nat) (w : Q') : Type where
  turan : forall t, 1 <= t -> t < 2 * N ->
    boxTailBase N w (t - 1) * boxTailLeft N w t <=
      (w * boxTailBase N w t) * boxTailLeft N w (t - 1)

private theorem qpow_two_eqv_mul (w : Q') :
    qpow w 2 ≈ w * w := by
  change ((1 : Q') * w) * w ≈ w * w
  exact Q'.mul_eqv_congr_right _ _ w (Q'.one_mul_eqv w)

private theorem mul4_cycle_eqv (X C Y D : Q') :
    (X * C) * (Y * D) ≈ (C * Y) * (X * D) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (Y * D) (Q'.mul_comm_eqv X C)) ?_
  exact mul_swap4 C X Y D

private theorem mul5_halfTime_eqv (w Y B E C : Q') :
    ((w * Y) * B) * ((w * E) * C) ≈
      (C * Y) * (((w * w) * E) * B) := by
  have h0 : ((w * Y) * B) * ((w * E) * C) ≈
      (((w * Y) * (w * E)) * (B * C)) :=
    mul_swap4 (w * Y) B (w * E) C
  have h1 : ((w * Y) * (w * E)) * (B * C) ≈
      (((w * w) * (Y * E)) * (B * C)) :=
    Q'.mul_eqv_congr_right _ _ (B * C) (mul_swap4 w Y w E)
  have h2 : ((w * w) * (Y * E)) * (B * C) ≈
      (((w * w) * B) * ((Y * E) * C)) :=
    mul_swap4 (w * w) (Y * E) B C
  have h3 : ((w * w) * B) * ((Y * E) * C) ≈
      (((Y * E) * C) * ((w * w) * B)) :=
    Q'.mul_comm_eqv _ _
  have hfirst : (Y * E) * C ≈ (C * Y) * E :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (Y * E) C)
      (Q'.eqv_symm (Q'.mul_assoc_eqv C Y E))
  have h4 : ((Y * E) * C) * ((w * w) * B) ≈
      (((C * Y) * E) * ((w * w) * B)) :=
    Q'.mul_eqv_congr_right _ _ ((w * w) * B) hfirst
  have h5 : ((C * Y) * E) * ((w * w) * B) ≈
      (((C * Y) * (w * w)) * (E * B)) :=
    mul_swap4 (C * Y) E (w * w) B
  have h6 : ((C * Y) * (w * w)) * (E * B) ≈
      (C * Y) * ((w * w) * (E * B)) :=
    Q'.mul_assoc_eqv (C * Y) (w * w) (E * B)
  have h7 : (C * Y) * ((w * w) * (E * B)) ≈
      (C * Y) * (((w * w) * E) * B) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (w * w) E B))
  exact Q'.eqv_trans _ _ _ h0
    (Q'.eqv_trans _ _ _ h1
      (Q'.eqv_trans _ _ _ h2
        (Q'.eqv_trans _ _ _ h3
          (Q'.eqv_trans _ _ _ h4
            (Q'.eqv_trans _ _ _ h5
              (Q'.eqv_trans _ _ _ h6 h7))))))

/-! ## 2. Two adjacent rows generate the odd row -/

/-- Abstract two-row cancellation: multiply two adjacent `w` rows, permute
the scalar factors, and cancel the strictly positive overlap `C*Y`. -/
private theorem odd_cross_of_two_halfTime_rows
    {w X C Y D B E : Q'}
    (hw0 : (0 : Q') <= w)
    (hC : (0 : Q') < C) (hY : (0 : Q') < Y)
    (hD : (0 : Q') <= D) (hB : (0 : Q') <= B)
    (hfirst : X * C <= (w * Y) * B)
    (hsecond : Y * D <= (w * E) * C) :
    X * D <= (qpow w 2 * E) * B := by
  have hleftNonneg : (0 : Q') <= Y * D :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt hY) hD
  have hrightNonneg : (0 : Q') <= (w * Y) * B :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ hw0 (Q'.le_of_lt hY)) hB
  have hscaledFirst :
      (X * C) * (Y * D) <= ((w * Y) * B) * (Y * D) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hfirst hleftNonneg
  have hscaledSecond :
      ((w * Y) * B) * (Y * D) <=
        ((w * Y) * B) * ((w * E) * C) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hsecond hrightNonneg
  have hproduct :
      (X * C) * (Y * D) <= ((w * Y) * B) * ((w * E) * C) :=
    Q'.le_trans' _ _ _ hscaledFirst hscaledSecond
  have hrightMul :
      (C * Y) * (((w * w) * E) * B) ≈
        (C * Y) * ((qpow w 2 * E) * B) := by
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_right _ _ B
        (Q'.mul_eqv_congr_right _ _ E
          (Q'.eqv_symm (qpow_two_eqv_mul w))))
  have hcancelReady :
      (C * Y) * (X * D) <=
        (C * Y) * ((qpow w 2 * E) * B) :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (mul4_cycle_eqv X C Y D))
      (Q'.le_trans' _ _ _ hproduct
        (Q'.le_of_eqv
          (Q'.eqv_trans _ _ _ (mul5_halfTime_eqv w Y B E C)
            hrightMul)))
  exact Q'.le_of_mul_le_mul_left hcancelReady (Q'.mul_pos hC hY)

private theorem boxTailBase_pos {N : Nat} {w : Q'}
    (hwpos : (0 : Q') < w) (s : Nat) (hs : s <= 2 * N) :
    (0 : Q') < boxTailBase N w s := by
  unfold boxTailBase
  have hbond : (0 : Q') < bondMovedCoeff N w 2 s :=
    bondMovedCoeff_p2_pos_full_support hwpos hs
  have hbox : (0 : Q') < boxSum w N s :=
    Q'.pos_of_lt_of_le hbond
      (Q'.le_of_eqv (bondMovedCoeff_eq_boxSum N s))
  exact Q'.mul_pos (dimQ_pos (s + 1)) hbox

private theorem boxTailLeft_pos {N : Nat} {w : Q'}
    (hwpos : (0 : Q') < w) (s : Nat) (hs : s < 2 * N) :
    (0 : Q') < boxTailLeft N w s := by
  unfold boxTailLeft
  have hbond : (0 : Q') < bondMovedCoeff N w 2 (s + 1) :=
    bondMovedCoeff_p2_pos_full_support hwpos (by omega)
  have hbox : (0 : Q') < boxSum w N (s + 1) :=
    Q'.pos_of_lt_of_le hbond
      (Q'.le_of_eqv (bondMovedCoeff_eq_boxSum N (s + 1)))
  exact Q'.mul_pos (dimQ_pos s) hbox

/-- The odd `w^2` row follows from the adjacent rows centred at `s+1` and
`s+2`; it is not an independent analytic input. -/
theorem P2HalfTimeBoxStrongTuran.oddStep {N : Nat} {w : Q'}
    (hwpos : (0 : Q') < w) (T : P2HalfTimeBoxStrongTuran N w)
    (s : Nat) (hs : s + 2 < 2 * N) :
    boxTailBase N w s * boxTailLeft N w (s + 2) <=
      (qpow w 2 * boxTailBase N w (s + 2)) *
        boxTailLeft N w s := by
  let X := boxTailBase N w s
  let C := boxTailLeft N w (s + 1)
  let Y := boxTailBase N w (s + 1)
  let D := boxTailLeft N w (s + 2)
  let B := boxTailLeft N w s
  let E := boxTailBase N w (s + 2)
  have hfirst : X * C <= (w * Y) * B := by
    dsimp only [X, C, Y, B]
    simpa only [Nat.add_sub_cancel] using
      T.turan (s + 1) (by omega) (by omega)
  have hsecond : Y * D <= (w * E) * C := by
    dsimp only [Y, D, E, C]
    have hsub : s + 2 - 1 = s + 1 := by omega
    simpa only [hsub] using T.turan (s + 2) (by omega) hs
  have hcore := odd_cross_of_two_halfTime_rows
    (Q'.le_of_lt hwpos)
    (boxTailLeft_pos hwpos (s + 1) (by omega))
    (boxTailBase_pos hwpos (s + 1) (by omega))
    (Q'.le_of_lt (boxTailLeft_pos hwpos (s + 2) hs))
    (Q'.le_of_lt (boxTailLeft_pos hwpos s (by omega)))
    hfirst hsecond
  simpa only [X, D, E, B] using hcore

/-- One all-row strong-Turan witness supplies the complete fixed-power parity
automaton.  The even bridge is one row; the odd step is the two-row
cancellation above. -/
def P2HalfTimeBoxStrongTuran.toTransitions {N : Nat} {w : Q'}
    (hwpos : (0 : Q') < w) (T : P2HalfTimeBoxStrongTuran N w) :
    P2HalfTimeBoxCoreParityTransitions N w where
  oddStep := fun m hm => by
    have h := T.oddStep hwpos (2 * m + 1) (by omega)
    have hindex : 2 * m + 1 + 2 = 2 * m + 3 := by omega
    simpa only [hindex] using h
  evenBridge := fun m hm1 hm => T.turan (2 * m) (by omega) hm

/-! ## 3. One pure-natural cell per row -/

/-- Cleared natural-number form of the adjacent half-time strong-Turan row
at centre `t`. -/
def physicalHalfTimeBoxTuranAt (k t : Nat) : Prop :=
  integralBoxCrossAt
    (physicalWeightNum k) (physicalWeightDen k)
    (physicalWeightNum k) (physicalWeightDen k)
    (blockNcut k) 1 (t - 1) t t (t - 1)

instance physicalHalfTimeBoxTuranAtDecidable (k t : Nat) :
    Decidable (physicalHalfTimeBoxTuranAt k t) := by
  unfold physicalHalfTimeBoxTuranAt
  infer_instance

/-- Generic soundness of one cleared adjacent row. -/
theorem physicalHalfTimeBoxTuranAt_sound (k t : Nat)
    (h : physicalHalfTimeBoxTuranAt k t) :
    boxTailBase (blockNcut k) (blockWeight k) (t - 1) *
        boxTailLeft (blockNcut k) (blockWeight k) t <=
      (blockWeight k *
          boxTailBase (blockNcut k) (blockWeight k) t) *
        boxTailLeft (blockNcut k) (blockWeight k) (t - 1) := by
  have hraw := integralBoxCrossAt_sound_of_base
    (physicalWeightNum k) (physicalWeightDen k)
    (physicalWeightNum k) (physicalWeightDen k)
    (blockNcut k) 1 (t - 1) t t (t - 1)
    (physicalWeightDen_pos k) (physicalWeightDen_pos k)
    (blockWeight k) (blockWeight_eqv_closed k)
    (blockWeight k) (blockWeight_eqv_closed k) h
  have hone : qpow (blockWeight k) 1 ≈ blockWeight k := by
    unfold qpow
    exact Q'.one_mul_eqv _
  have hright :
      (qpow (blockWeight k) 1 *
          boxTailBase (blockNcut k) (blockWeight k) t) *
        boxTailLeft (blockNcut k) (blockWeight k) (t - 1) ≈
      (blockWeight k *
          boxTailBase (blockNcut k) (blockWeight k) t) *
        boxTailLeft (blockNcut k) (blockWeight k) (t - 1) :=
    Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hone)
  exact Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv hright)

/-! ## 4. Physical all-scale compiler -/

/-- The reduced physical frontier: one adjacent strong-Turan row at every
supported centre and every scale beginning at `k=4`. -/
structure BlockCompatibleP2HalfTimeStrongTuranFromFour : Type where
  turan : forall k, 4 <= k ->
    P2HalfTimeBoxStrongTuran (blockNcut k) (blockWeight k)

/-- Fully arithmetic form of the reduced frontier: one natural-number
cross-product at every supported centre. -/
structure BlockCompatibleP2HalfTimeIntegralStrongTuranFromFour : Type where
  turan : forall k t, 4 <= k -> 1 <= t -> t < 2 * blockNcut k ->
    physicalHalfTimeBoxTuranAt k t

/-- The generic soundness theorem turns the pure-natural carrier into the
one-row rational strong-Turan family. -/
def BlockCompatibleP2HalfTimeIntegralStrongTuranFromFour.toStrongTuran
    (T : BlockCompatibleP2HalfTimeIntegralStrongTuranFromFour) :
    BlockCompatibleP2HalfTimeStrongTuranFromFour where
  turan := fun k hk => {
    turan := fun t ht htN =>
      physicalHalfTimeBoxTuranAt_sound k t (T.turan k t hk ht htN)
  }

/-- Install the one-row family into the already checked physical heads and
the heat-matched parity compiler. -/
def BlockCompatibleP2HalfTimeStrongTuranFromFour.toTransitions
    (T : BlockCompatibleP2HalfTimeStrongTuranFromFour) :
    BlockCompatibleP2HalfTimeTransitionsFromFour where
  transitions := fun k hk =>
    (T.turan k hk).toTransitions (blockWeight_pos k)
  headSix := physical_halfTime_box_head_of_linear 6
    physicalLinearHalfTimeHeadCheck_six
  headSeven := physical_halfTime_box_head_of_linear 7
    physicalLinearHalfTimeHeadCheck_seven

/-- The one-row physical frontier reaches the reviewed all-cutoff canonical
control family through the checked heads, parity automaton, and exact A1
strand reindex. -/
def BlockCompatibleP2HalfTimeStrongTuranFromFour.toControlFamily
    (T : BlockCompatibleP2HalfTimeStrongTuranFromFour) :
    P2RetunedBlockingDictionary.P2RetunedControlFamily :=
  T.toTransitions.toLineSumTail.toControlFamily

/-- The one-cross-product-per-row arithmetic frontier reaches the reviewed
all-cutoff canonical control family. -/
def BlockCompatibleP2HalfTimeIntegralStrongTuranFromFour.toControlFamily
    (T : BlockCompatibleP2HalfTimeIntegralStrongTuranFromFour) :
    P2RetunedBlockingDictionary.P2RetunedControlFamily :=
  T.toStrongTuran.toControlFamily

end YMGap.Continuum.P2HalfTimeStrongTuranCompiler

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeStrongTuranCompiler.P2HalfTimeBoxStrongTuran.oddStep
#print axioms YMGap.Continuum.P2HalfTimeStrongTuranCompiler.P2HalfTimeBoxStrongTuran.toTransitions
#print axioms YMGap.Continuum.P2HalfTimeStrongTuranCompiler.physicalHalfTimeBoxTuranAt_sound
#print axioms YMGap.Continuum.P2HalfTimeStrongTuranCompiler.BlockCompatibleP2HalfTimeStrongTuranFromFour.toTransitions
#print axioms YMGap.Continuum.P2HalfTimeStrongTuranCompiler.BlockCompatibleP2HalfTimeStrongTuranFromFour.toControlFamily
#print axioms YMGap.Continuum.P2HalfTimeStrongTuranCompiler.BlockCompatibleP2HalfTimeIntegralStrongTuranFromFour.toStrongTuran
#print axioms YMGap.Continuum.P2HalfTimeStrongTuranCompiler.BlockCompatibleP2HalfTimeIntegralStrongTuranFromFour.toControlFamily
