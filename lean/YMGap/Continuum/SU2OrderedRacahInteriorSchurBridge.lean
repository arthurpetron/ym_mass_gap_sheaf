/-
# Interior Schur/Gram bridge for ordered SU(2) recoupling

The fixed-output Schur theorem already expands every left-associated channel
in the complete finite family of right-associated channels.  This file proves
the missing abstract metric step: pairing that exact expansion against one
right channel reduces to a finite right-channel Gram row, and pairwise Gram
orthogonality collapses the row to the selected inverse Schur coefficient.

The result is division-free.  It isolates right-channel orthogonality as a
strictly smaller normalization input than the full factorial Racah identity.
As a non-boundary check, the complete `(2,2,1,1)` block (all external labels
positive) is instantiated and both corrected forward and inverse bridges are
kernel-checked on all four entries.
-/

import YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier
import YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge
import YMGap.Continuum.SU2TransvectantAllLabelGNSIsometryCompleted

namespace YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2GeneralHahnCumulativeTransform
open YMGap.Continuum.SU2TransvectantCentralChannelEquation
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2DirectRightFixedOutputReconstruction
open YMGap.Continuum.SU2FixedLeftRightAssociatorSchur
open YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge
open YMGap.Continuum.SU2OrderedFixedOutputFKernel
open YMGap.Continuum.SU2OrderedRacahMultiplicityFence
open YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier
open YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SixJKernel

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Bilinearity of the exact invariant pairing -/

/-- The exact invariant pairing respects a certified physical-box identity in
its first argument. -/
theorem triMapInner_congr_left {a b c d : Nat}
    {L L' R : BForm → BForm → BForm → BForm}
    (h : TriMapEqv a b c d L L') :
    triMapInner a b c d L R ≈ triMapInner a b c d L' R := by
  unfold triMapInner
  refine finSum_eqv_congr_lt _ _ (a + 1) (fun i hi => ?_)
  refine finSum_eqv_congr_lt _ _ (b + 1) (fun j hj => ?_)
  refine finSum_eqv_congr_lt _ _ (c + 1) (fun k hk => ?_)
  refine finSum_eqv_congr_lt _ _ (d + 1) (fun s hs => ?_)
  exact Q'.mul_eqv_congr_left
    (tvBinomQ a i * tvBinomQ b j * tvBinomQ c k *
      symMonomialNormSq d s) _ _
    (Q'.mul_eqv_congr_right _ _
      (R (mono i) (mono j) (mono k) s)
      (h i hi j hj k hk s hs))

/-- Additivity of the invariant pairing in its first argument. -/
theorem triMapInner_add_left (a b c d : Nat)
    (L M R : BForm → BForm → BForm → BForm) :
    triMapInner a b c d (fun x y z => addForm (L x y z) (M x y z)) R ≈
      triMapInner a b c d L R + triMapInner a b c d M R := by
  unfold triMapInner
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ _ (a + 1) (fun i hi => ?_))
    (RationalTail.finSum_add _ _ (a + 1))
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ _ (b + 1) (fun j hj => ?_))
    (RationalTail.finSum_add _ _ (b + 1))
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ _ (c + 1) (fun k hk => ?_))
    (RationalTail.finSum_add _ _ (c + 1))
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ _ (d + 1) (fun s hs => ?_))
    (RationalTail.finSum_add _ _ (d + 1))
  unfold addForm
  ring_qeqv

/-- Scalar linearity of the invariant pairing in its first argument. -/
theorem triMapInner_scale_left (a b c d : Nat) (q : Q')
    (L R : BForm → BForm → BForm → BForm) :
    triMapInner a b c d (fun x y z => scaleForm q (L x y z)) R ≈
      q * triMapInner a b c d L R := by
  unfold triMapInner
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ _ (a + 1) (fun i hi => ?_))
    (Q'.eqv_symm (RationalTail.const_mul_finSum _ q (a + 1)))
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ _ (b + 1) (fun j hj => ?_))
    (Q'.eqv_symm (RationalTail.const_mul_finSum _ q (b + 1)))
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ _ (c + 1) (fun k hk => ?_))
    (Q'.eqv_symm (RationalTail.const_mul_finSum _ q (c + 1)))
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ _ (d + 1) (fun s hs => ?_))
    (Q'.eqv_symm (RationalTail.const_mul_finSum _ q (d + 1)))
  unfold scaleForm
  ring_qeqv

/-- The zero trilinear map is orthogonal to every target map. -/
theorem triMapInner_zero_left (a b c d : Nat)
    (R : BForm → BForm → BForm → BForm) :
    triMapInner a b c d (fun _ _ _ => zeroF) R ≈ 0 := by
  have hzero : TriMapEqv a b c d
      (fun _ _ _ => zeroF)
      (fun _ _ _ => scaleForm 0 zeroF) := by
    intro i hi j hj k hk s hs
    unfold zeroF scaleForm
    exact Q'.eqv_symm (Q'.zero_mul_eqv 0)
  exact Q'.eqv_trans _ _ _ (triMapInner_congr_left hzero)
    (Q'.eqv_trans _ _ _
      (triMapInner_scale_left a b c d 0 (fun _ _ _ => zeroF) R)
      (Q'.zero_mul_eqv _))

/-! ## 2. Pairing a finite Schur expansion -/

/-- Pairing a finite packaged right-channel expansion is the corresponding
finite Gram-row dot product. -/
theorem triMapInner_rightChannelPrefix (a b c d N : Nat)
    (col : Nat → Nat) (coeff : Nat → Q')
    (R : BForm → BForm → BForm → BForm) :
    triMapInner a b c d (rightChannelPrefix a b c d N col coeff) R ≈
      finiteDot N coeff (fun q => triMapInner a b c d
        (triRight a b c d (rightChannelLabel b c (col q))) R) := by
  induction N generalizing col coeff with
  | zero =>
      exact triMapInner_zero_left a b c d R
  | succ N ih =>
      simp only [rightChannelPrefix, finiteDot]
      refine Q'.eqv_trans _ _ _
        (triMapInner_add_left a b c d _ _ R) ?_
      exact Q'.add_eqv_congr'
        (triMapInner_scale_left a b c d (coeff 0) _ R)
        (ih (fun q => col (q + 1)) (fun q => coeff (q + 1)))

private theorem finiteDot_congr (N : Nat)
    (row row' x x' : Nat → Q')
    (hterm : ∀ q, q < N → row q * x q ≈ row' q * x' q) :
    finiteDot N row x ≈ finiteDot N row' x' := by
  induction N generalizing row row' x x' with
  | zero => exact Q'.eqv_refl _
  | succ N ih =>
      simp only [finiteDot]
      exact Q'.add_eqv_congr'
        (hterm 0 (by omega))
        (ih (fun q => row (q + 1)) (fun q => row' (q + 1))
          (fun q => x (q + 1)) (fun q => x' (q + 1))
          (fun q hq => hterm (q + 1) (by omega)))

private theorem finiteDot_zero_right (N : Nat)
    (row x : Nat → Q') (hx : ∀ q, q < N → x q ≈ 0) :
    finiteDot N row x ≈ 0 := by
  induction N generalizing row x with
  | zero => exact Q'.eqv_refl _
  | succ N ih =>
      simp only [finiteDot]
      exact Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ (row 0 * 0) _
            (Q'.mul_eqv_congr_left (row 0) _ _ (hx 0 (by omega)))
            (Q'.mul_zero_eqv _))
          (ih (fun q => row (q + 1)) (fun q => x (q + 1))
            (fun q hq => hx (q + 1) (by omega))))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem finiteDot_onehot_weight : ∀ N target : Nat,
    target < N → ∀ coeff : Nat → Q', ∀ W : Q',
      finiteDot N coeff (fun q => if q = target then W else 0) ≈
        coeff target * W
  | 0, target, h, _, _ => by omega
  | N + 1, 0, _, coeff, W => by
      simp only [finiteDot, if_pos]
      have htail : finiteDot N (fun q => coeff (q + 1))
          (fun q => if q + 1 = 0 then W else 0) ≈ 0 := by
        exact finiteDot_zero_right N _ _ (fun q hq => by
          rw [if_neg (by omega)]
          exact Q'.eqv_refl _)
      exact Q'.eqv_trans _ (coeff 0 * W + 0) _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) htail)
        (Q'.eqv_of_eq (Q'.add_zero' _))
  | N + 1, target + 1, h, coeff, W => by
      simp only [finiteDot, if_neg (by omega : ¬ 0 = target + 1)]
      have ih := finiteDot_onehot_weight N target (by omega)
        (fun q => coeff (q + 1)) W
      have htail : finiteDot N (fun q => coeff (q + 1))
          (fun q => if q + 1 = target + 1 then W else 0) ≈
          coeff (target + 1) * W := by
        refine Q'.eqv_trans _
          (finiteDot N (fun q => coeff (q + 1))
            (fun q => if q = target then W else 0)) _ ?_ ih
        exact finiteDot_congr N _ _ _ _ (fun q hq => by
          by_cases h : q = target
          · rw [if_pos h, if_pos (by omega)]
            exact Q'.eqv_refl _
          · rw [if_neg h, if_neg (by omega)]
            exact Q'.eqv_refl _)
      exact Q'.eqv_trans _ (0 + coeff (target + 1) * W) _
        (Q'.add_eqv_congr' (Q'.mul_zero_eqv _) htail)
        (Q'.eqv_of_eq (Q'.zero_add' _))

/-- A Schur row paired with a Gram-orthogonal target channel collapses to
the selected coefficient times the target channel's exact Gram weight. -/
theorem schur_pairing_of_right_orthogonality {a b c d N target : Nat}
    (col : Nat → Nat) (coeff : Nat → Q')
    (L : BForm → BForm → BForm → BForm)
    (qR : FixedRightCGChannel a b c d)
    (htarget : target < N)
    (hrow : TriMapEqv a b c d L
      (rightChannelPrefix a b c d N col coeff))
    (horth : ∀ q, q < N →
      triMapInner a b c d
          (triRight a b c d (rightChannelLabel b c (col q)))
          (triRight a b c d qR.intermediate) ≈
        if q = target then
          triRightChannelWeight a b c d qR.intermediate else 0) :
    triMapInner a b c d L (triRight a b c d qR.intermediate) ≈
      coeff target * triRightChannelWeight a b c d qR.intermediate := by
  refine Q'.eqv_trans _ _ _ (triMapInner_congr_left hrow) ?_
  refine Q'.eqv_trans _ _ _
    (triMapInner_rightChannelPrefix a b c d N col coeff _) ?_
  refine Q'.eqv_trans _
    (finiteDot N coeff (fun q => if q = target then
      triRightChannelWeight a b c d qR.intermediate else 0)) _ ?_ ?_
  · exact finiteDot_congr N coeff coeff _ _
      (fun q hq => Q'.mul_eqv_congr_left (coeff q) _ _ (horth q hq))
  · exact finiteDot_onehot_weight N target htarget coeff _

/-! ## 3. The canonical all-label Schur row -/

/-- The concrete channel at one index of the canonical duplicate-free right
channel enumeration attached to a fixed left channel. -/
def enumeratedRightChannel {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d) (q : Nat) :
    FixedRightCGChannel a b c d :=
  fixedRightChannelAt (fixedRightFallbackOfFixedLeft qL)
    (fixedRightChannels a b c d) q

/-- The exact right-Gram condition needed to collapse the canonical Schur row
at one selected target index.  Unlike a Racah formula, this contains no
factorial kernel and no comparison between bracketings. -/
def EnumeratedRightGramOrthogonalAt {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d) (target : Nat) : Prop :=
  target < (fixedRightChannels a b c d).length ∧
  ∀ q, q < (fixedRightChannels a b c d).length →
    triMapInner a b c d
        (triRight a b c d (enumeratedRightChannel qL q).intermediate)
        (triRight a b c d
          (enumeratedRightChannel qL target).intermediate) ≈
      if q = target then
        triRightChannelWeight a b c d
          (enumeratedRightChannel qL target).intermediate else 0

/-- **All-label inverse Schur cross normalization from right orthogonality.**
The already-proved canonical Schur expansion and one exact Gram row imply that
the physical left/right cross pairing is the selected inverse coefficient
times the target right-channel weight. -/
theorem fixedLeft_schur_pairing_of_enumerated_right_orthogonality
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d) (target : Nat)
    (horth : EnumeratedRightGramOrthogonalAt qL target) :
    triMapInner a b c d (triLeft a b c d qL.intermediate)
        (triRight a b c d
          (enumeratedRightChannel qL target).intermediate) ≈
      fixedLeftRightDiagonalCoeff qL
          (enumeratedRightChannel qL target) 0 *
        triRightChannelWeight a b c d
          (enumeratedRightChannel qL target).intermediate := by
  let qR := enumeratedRightChannel qL target
  have h := schur_pairing_of_right_orthogonality
    (a := a) (b := b) (c := c) (d := d)
    (N := (fixedRightChannels a b c d).length) (target := target)
    (fun q => (enumeratedRightChannel qL q).p)
    (fun q => fixedLeftRightDiagonalCoeff qL
      (enumeratedRightChannel qL q) 0)
    (triLeft a b c d qL.intermediate) qR horth.1
    (by
      simpa only [enumeratedRightChannel] using
        fixedLeft_directRightFixedOutput_schur qL)
    (fun q hq => by
      simpa only [qR, rightChannelLabel,
        FixedRightCGChannel.intermediate] using horth.2 q hq)
  exact h

/-- Division-free inverse cross normalization for the collapsed factorial
carrier at the canonical target index. -/
theorem collapsed_cross_inverse_normalization_of_right_orthogonality
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d) (target : Nat)
    (horth : EnumeratedRightGramOrthogonalAt qL target) :
    collapsedFactorialCrossSum qL (enumeratedRightChannel qL target) ≈
      triRightChannelWeight a b c d
          (enumeratedRightChannel qL target).intermediate *
        fixedLeftRightDiagonalCoeff qL
          (enumeratedRightChannel qL target) 0 := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (triCrossChannelWeight_eq_collapsedFactorialCrossSum qL
        (enumeratedRightChannel qL target)))
    (Q'.eqv_trans _ _ _
      (fixedLeft_schur_pairing_of_enumerated_right_orthogonality
        qL target horth)
      (Q'.mul_comm_eqv _ _))

/-- The corrected inverse bridge and its Schur/orthogonality normalization
imply the same explicit squared factorial target as the corrected forward
bridge.  This proves that the two normalizations meet at one common carrier
without division or cancellation. -/
theorem collapsedRacahSquare_of_inverse_normalization_and_bridge
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d)
    (hcross : collapsedFactorialCrossSum qL qR ≈
      triRightChannelWeight a b c d qR.intermediate *
        fixedLeftRightDiagonalCoeff qL qR 0)
    (hbridge : InverseSchurGramRacahBridgeAt qL qR) :
    CollapsedRacahSquareAt qL qR := by
  let C := collapsedFactorialCrossSum qL qR
  let WL := triLeftChannelWeight a b c d qL.intermediate
  let WR := triRightChannelWeight a b c d qR.intermediate
  let K := fixedLeftRightDiagonalCoeff qL qR 0
  let P := racahKernel6 a b c d qL.intermediate qR.intermediate
  have hc2 : C * C ≈ (WR * K) * (WR * K) := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right C (WR * K) C hcross)
      (Q'.mul_eqv_congr_left (WR * K) C (WR * K) hcross)
  have hrearrange : (WR * K) * (WR * K) ≈ WR * (WR * (K * K)) := by
    ring_qeqv
  have hscaled : WR * (WL * P) ≈ WR * (WR * (K * K)) :=
    Q'.mul_eqv_congr_left WR _ _ hbridge
  have htarget : WL * (WR * P) ≈ WR * (WL * P) := by
    ring_qeqv
  exact Q'.eqv_trans _ _ _ hc2
    (Q'.eqv_trans _ _ _ hrearrange
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hscaled)
        (Q'.eqv_symm htarget)))

/-- Conversely, a strictly positive right Gram weight lets the common
factorial square target and inverse Schur cross normalization discharge the
corrected inverse bridge by constructive positive-factor cancellation. -/
theorem inverseSchurGramRacahBridge_of_collapsed_square
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d)
    (hWR : (0 : Q') < triRightChannelWeight a b c d qR.intermediate)
    (hcross : collapsedFactorialCrossSum qL qR ≈
      triRightChannelWeight a b c d qR.intermediate *
        fixedLeftRightDiagonalCoeff qL qR 0)
    (hsquare : CollapsedRacahSquareAt qL qR) :
    InverseSchurGramRacahBridgeAt qL qR := by
  let C := collapsedFactorialCrossSum qL qR
  let WL := triLeftChannelWeight a b c d qL.intermediate
  let WR := triRightChannelWeight a b c d qR.intermediate
  let K := fixedLeftRightDiagonalCoeff qL qR 0
  let P := racahKernel6 a b c d qL.intermediate qR.intermediate
  have hc2 : C * C ≈ (WR * K) * (WR * K) := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right C (WR * K) C hcross)
      (Q'.mul_eqv_congr_left (WR * K) C (WR * K) hcross)
  have hrearrange : (WR * K) * (WR * K) ≈ WR * (WR * (K * K)) := by
    ring_qeqv
  have htarget : WL * (WR * P) ≈ WR * (WL * P) := by
    ring_qeqv
  have hscaled : WR * (WL * P) ≈ WR * (WR * (K * K)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm htarget)
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hsquare)
        (Q'.eqv_trans _ _ _ hc2 hrearrange))
  exact Q'.mul_left_cancel_of_pos hWR hscaled

/-- The forward normalization has the symmetric converse: positivity of the
left Gram weight cancels the source factor and recovers the corrected forward
bridge from the same common squared factorial target. -/
theorem gramWeightedRacahBridge_of_collapsed_square
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d)
    (hWL : (0 : Q') < triLeftChannelWeight a b c d qL.intermediate)
    (hcross : CollapsedCrossFNormalizationAt qL qR)
    (hsquare : CollapsedRacahSquareAt qL qR) :
    GramWeightedRacahBridgeAt qL qR := by
  let C := collapsedFactorialCrossSum qL qR
  let WL := triLeftChannelWeight a b c d qL.intermediate
  let WR := triRightChannelWeight a b c d qR.intermediate
  let F := fixedOrderedFCoefficient qL qR
  let P := racahKernel6 a b c d qL.intermediate qR.intermediate
  have hc2 : C * C ≈ (WL * F) * (WL * F) := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right C (WL * F) C hcross)
      (Q'.mul_eqv_congr_left (WL * F) C (WL * F) hcross)
  have hrearrange : (WL * F) * (WL * F) ≈ WL * (WL * (F * F)) := by
    ring_qeqv
  have hscaled : WL * (WR * P) ≈ WL * (WL * (F * F)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hsquare)
      (Q'.eqv_trans _ _ _ hc2 hrearrange)
  exact Q'.mul_left_cancel_of_pos hWL hscaled

/-! ## 4. Concrete all-positive interior block -/

/-- Left channel `e=0` of the all-positive `(2,2,1,1)` block. -/
def mixed221Left0 : FixedLeftCGChannel 2 2 1 1 where
  k := 2
  k_le := by decide
  r := 0
  r_le := by decide
  degree_eq := by decide

/-- Left channel `e=2` of the all-positive `(2,2,1,1)` block. -/
def mixed221Left2 : FixedLeftCGChannel 2 2 1 1 where
  k := 1
  k_le := by decide
  r := 1
  r_le := by decide
  degree_eq := by decide

/-- Right channel `f=1` of the all-positive `(2,2,1,1)` block. -/
def mixed221Right1 : FixedRightCGChannel 2 2 1 1 where
  p := 1
  p_le := by decide
  r := 1
  r_le := by decide
  degree_eq := by decide

/-- Right channel `f=3` of the all-positive `(2,2,1,1)` block. -/
def mixed221Right3 : FixedRightCGChannel 2 2 1 1 where
  p := 0
  p_le := by decide
  r := 2
  r_le := by decide
  degree_eq := by decide

/-- Machine guard that this block contains a strictly interior channel entry:
all four external labels and the selected left/right intermediate labels are
positive. -/
theorem mixed221_strictly_positive_entry :
    0 < 2 ∧ 0 < 2 ∧ 0 < 1 ∧ 0 < 1 ∧
      0 < mixed221Left2.intermediate ∧
      0 < mixed221Right1.intermediate := by
  decide

/-- The physical inverse Schur coefficients of the mixed block are precisely
the previously derived transvectant associator rows. -/
theorem mixed221_inverseSchur_entries :
    fixedLeftRightDiagonalCoeff mixed221Left0 mixed221Right1 0 ≈ -twoThirds ∧
    fixedLeftRightDiagonalCoeff mixed221Left0 mixed221Right3 0 ≈
      YMGap.Continuum.SU2SpinOneLabelWiredPentagon.oneThird ∧
    fixedLeftRightDiagonalCoeff mixed221Left2 mixed221Right1 0 ≈ fourThirds ∧
    fixedLeftRightDiagonalCoeff mixed221Left2 mixed221Right3 0 ≈
      YMGap.Continuum.SU2SpinOneLabelWiredPentagon.oneThird := by
  decide

/-- Exact right-channel Gram orthogonality for the genuinely mixed interior
block, recovered from the invariant transvectant pairing. -/
theorem mixed221_right_gram_orthogonal :
    triMapInner 2 2 1 1
        (triRight 2 2 1 1 mixed221Right1.intermediate)
        (triRight 2 2 1 1 mixed221Right1.intermediate) ≈ 72 ∧
    triMapInner 2 2 1 1
        (triRight 2 2 1 1 mixed221Right1.intermediate)
        (triRight 2 2 1 1 mixed221Right3.intermediate) ≈ 0 ∧
    triMapInner 2 2 1 1
        (triRight 2 2 1 1 mixed221Right3.intermediate)
        (triRight 2 2 1 1 mixed221Right1.intermediate) ≈ 0 ∧
    triMapInner 2 2 1 1
        (triRight 2 2 1 1 mixed221Right3.intermediate)
        (triRight 2 2 1 1 mixed221Right3.intermediate) ≈ 576 := by
  decide

/-- The first canonical target index of the mixed row satisfies the abstract
all-label right-Gram condition.  The enumeration is computed only to identify
its two indices; the Gram entries are the physical invariant pairings above. -/
theorem mixed221_enumerated_right_orthogonal_0 :
    EnumeratedRightGramOrthogonalAt mixed221Left0 0 := by
  constructor
  · decide
  · intro q hq
    have hlen : (fixedRightChannels 2 2 1 1).length = 2 := by decide
    rw [hlen] at hq
    have hcases : q = 0 ∨ q = 1 := by omega
    rcases hcases with hq0 | hq1
    · subst q
      decide
    · subst q
      decide

/-- The second canonical target index of the same mixed row also satisfies
the abstract right-Gram condition. -/
theorem mixed221_enumerated_right_orthogonal_1 :
    EnumeratedRightGramOrthogonalAt mixed221Left0 1 := by
  constructor
  · decide
  · intro q hq
    have hlen : (fixedRightChannels 2 2 1 1).length = 2 := by decide
    rw [hlen] at hq
    have hcases : q = 0 ∨ q = 1 := by omega
    rcases hcases with hq0 | hq1
    · subst q
      decide
    · subst q
      decide

/-- On the mixed row the abstract Schur/orthogonality theorem supplies both
inverse cross normalizations, rather than taking them as separate identities. -/
theorem mixed221_inverse_cross_normalizations_from_schur :
    collapsedFactorialCrossSum mixed221Left0
        (enumeratedRightChannel mixed221Left0 0) ≈
      triRightChannelWeight 2 2 1 1
          (enumeratedRightChannel mixed221Left0 0).intermediate *
        fixedLeftRightDiagonalCoeff mixed221Left0
          (enumeratedRightChannel mixed221Left0 0) 0 ∧
    collapsedFactorialCrossSum mixed221Left0
        (enumeratedRightChannel mixed221Left0 1) ≈
      triRightChannelWeight 2 2 1 1
          (enumeratedRightChannel mixed221Left0 1).intermediate *
        fixedLeftRightDiagonalCoeff mixed221Left0
          (enumeratedRightChannel mixed221Left0 1) 0 := by
  exact ⟨
    collapsed_cross_inverse_normalization_of_right_orthogonality
      mixed221Left0 0 mixed221_enumerated_right_orthogonal_0,
    collapsed_cross_inverse_normalization_of_right_orthogonality
      mixed221Left0 1 mixed221_enumerated_right_orthogonal_1⟩

/-- On the genuine all-positive row, the independently checked factorial
square plus Schur-derived cross normalization and positive target Gram weights
discharge both corrected inverse bridges through the abstract cancellation
theorem.  No bridge is used to prove its own premise. -/
theorem mixed221_inverse_bridges_from_schur_and_factorial_square :
    InverseSchurGramRacahBridgeAt mixed221Left0
        (enumeratedRightChannel mixed221Left0 0) ∧
    InverseSchurGramRacahBridgeAt mixed221Left0
        (enumeratedRightChannel mixed221Left0 1) := by
  constructor
  · exact inverseSchurGramRacahBridge_of_collapsed_square
      mixed221Left0 (enumeratedRightChannel mixed221Left0 0)
      (by decide) mixed221_inverse_cross_normalizations_from_schur.1 (by
        unfold CollapsedRacahSquareAt
        decide)
  · exact inverseSchurGramRacahBridge_of_collapsed_square
      mixed221Left0 (enumeratedRightChannel mixed221Left0 1)
      (by decide) mixed221_inverse_cross_normalizations_from_schur.2 (by
        unfold CollapsedRacahSquareAt
        decide)

/-- The corrected forward Gram/Racah normalization holds on every entry of the
non-boundary `(2,2,1,1)` block. -/
theorem mixed221_forward_gramRacahBridges :
    GramWeightedRacahBridgeAt mixed221Left0 mixed221Right1 ∧
    GramWeightedRacahBridgeAt mixed221Left0 mixed221Right3 ∧
    GramWeightedRacahBridgeAt mixed221Left2 mixed221Right1 ∧
    GramWeightedRacahBridgeAt mixed221Left2 mixed221Right3 := by
  constructor
  · exact gramWeightedRacahBridge_of_collapsed_square
      mixed221Left0 mixed221Right1 (by decide)
      (by unfold CollapsedCrossFNormalizationAt; decide)
      (by unfold CollapsedRacahSquareAt; decide)
  · constructor
    · exact gramWeightedRacahBridge_of_collapsed_square
        mixed221Left0 mixed221Right3 (by decide)
        (by unfold CollapsedCrossFNormalizationAt; decide)
        (by unfold CollapsedRacahSquareAt; decide)
    · constructor
      · exact gramWeightedRacahBridge_of_collapsed_square
          mixed221Left2 mixed221Right1 (by decide)
          (by unfold CollapsedCrossFNormalizationAt; decide)
          (by unfold CollapsedRacahSquareAt; decide)
      · exact gramWeightedRacahBridge_of_collapsed_square
          mixed221Left2 mixed221Right3 (by decide)
          (by unfold CollapsedCrossFNormalizationAt; decide)
          (by unfold CollapsedRacahSquareAt; decide)

/-- The corrected inverse Schur Gram/Racah normalization holds on every entry
of the same all-positive interior block. -/
theorem mixed221_inverse_gramRacahBridges :
    InverseSchurGramRacahBridgeAt mixed221Left0 mixed221Right1 ∧
    InverseSchurGramRacahBridgeAt mixed221Left0 mixed221Right3 ∧
    InverseSchurGramRacahBridgeAt mixed221Left2 mixed221Right1 ∧
    InverseSchurGramRacahBridgeAt mixed221Left2 mixed221Right3 := by
  constructor
  · exact inverseSchurGramRacahBridge_of_collapsed_square
      mixed221Left0 mixed221Right1 (by decide)
      (by decide) (by unfold CollapsedRacahSquareAt; decide)
  · constructor
    · exact inverseSchurGramRacahBridge_of_collapsed_square
        mixed221Left0 mixed221Right3 (by decide)
        (by decide) (by unfold CollapsedRacahSquareAt; decide)
    · constructor
      · exact inverseSchurGramRacahBridge_of_collapsed_square
          mixed221Left2 mixed221Right1 (by decide)
          (by decide) (by unfold CollapsedRacahSquareAt; decide)
      · exact inverseSchurGramRacahBridge_of_collapsed_square
          mixed221Left2 mixed221Right3 (by decide)
          (by decide) (by unfold CollapsedRacahSquareAt; decide)

end YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge

#print axioms YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge.triMapInner_congr_left
#print axioms YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge.triMapInner_add_left
#print axioms YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge.triMapInner_scale_left
#print axioms YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge.triMapInner_rightChannelPrefix
#print axioms YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge.schur_pairing_of_right_orthogonality
#print axioms YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge.fixedLeft_schur_pairing_of_enumerated_right_orthogonality
#print axioms YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge.collapsed_cross_inverse_normalization_of_right_orthogonality
#print axioms YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge.collapsedRacahSquare_of_inverse_normalization_and_bridge
#print axioms YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge.inverseSchurGramRacahBridge_of_collapsed_square
#print axioms YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge.gramWeightedRacahBridge_of_collapsed_square
#print axioms YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge.mixed221_strictly_positive_entry
#print axioms YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge.mixed221_inverseSchur_entries
#print axioms YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge.mixed221_right_gram_orthogonal
#print axioms YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge.mixed221_enumerated_right_orthogonal_0
#print axioms YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge.mixed221_enumerated_right_orthogonal_1
#print axioms YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge.mixed221_inverse_cross_normalizations_from_schur
#print axioms YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge.mixed221_inverse_bridges_from_schur_and_factorial_square
#print axioms YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge.mixed221_forward_gramRacahBridges
#print axioms YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge.mixed221_inverse_gramRacahBridges
