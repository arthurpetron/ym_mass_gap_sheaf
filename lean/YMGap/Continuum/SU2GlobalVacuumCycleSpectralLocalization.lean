/-
# Located spectrum of the gauge-compatible SU(2) cycle quotient

`SU2GlobalVacuumCycleQuotient` constructs the genuine common-label quotient
for every nonempty bivalent shared-link cycle and proves its uniform `1/64`
squared-norm contraction after the unique global vacuum loop is removed.
This file identifies that contraction with a concrete finite diagonal
self-adjoint operator.

For a nonempty link-elimination order `l :: rest`, label `s` has transfer
eigenvalue `cycleEigen (l :: rest) s`.  The squared-transfer spectral model
uses its square, and assigns eigenvalue zero to the removed vacuum label.
Its spectral weight is the exact square of the globally projected cycle
coefficient.  Consequently `corr 0` is the projected cycle norm and `corr 1`
is the norm after transferring the same projected state on both sides.

Every nonvacuum squared eigenvalue is at most `(1/8)^2 = 1/64`, uniformly in
the number of links and the channel cutoff.  Hence the constructed finite
operator has a located gap margin exactly `63/64`.

Honest scope: this closes spectral localization for every bivalent cycle.
Trivalent and higher-valence spin networks still require the label-dependent
recoupling/F-move compatibility of their intertwiner spaces.
-/

import YMGap.Continuum.SU2GlobalVacuumCycleQuotient
import YMGap.Continuum.CompactTransferGNS

namespace YMGap.Continuum.SU2GlobalVacuumCycleSpectralLocalization

set_option maxHeartbeats 800000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactTransferGNS
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2GlobalVacuumCycleQuotient

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    (a * b) ≈ (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-! ## Exact cycle eigenvalue bounds -/

/-- Every product of nonnegative link eigenvalues is nonnegative. -/
theorem cycleEigen_nonneg_all (order : List Nat) (s : Nat) :
    (0 : Q') ≤ cycleEigen order s := by
  induction order with
  | nil =>
      change (0 : Q') ≤ 1
      decide
  | cons l rest ih =>
      change (0 : Q') ≤ eigA coupling s * cycleEigen rest s
      exact Q'.mul_nonneg _ _ (eigA_nonneg (by decide) s) ih

/-- Every cycle eigenvalue is at most the vacuum eigenvalue one. -/
theorem cycleEigen_le_one_all (order : List Nat) (s : Nat) :
    cycleEigen order s ≤ (1 : Q') := by
  induction order with
  | nil => exact Q'.le_refl' 1
  | cons l rest ih =>
      change eigA coupling s * cycleEigen rest s ≤ (1 : Q')
      have hm := Q'.mul_le_mul_of_nonneg
        (eigA_le_one (w := coupling) (by decide) (by decide) s) ih
        (by decide : (0 : Q') ≤ 1) (cycleEigen_nonneg_all rest s)
      exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.one_mul_eqv 1))

/-- A nonempty cycle has at least one exact heat-kernel factor, so every
nonvacuum eigenvalue is bounded by the fundamental edge `1/8`. -/
theorem cycleEigen_excited_le_eighth_all (l : Nat) (rest : List Nat)
    {s : Nat} (hs : 1 ≤ s) :
    cycleEigen (l :: rest) s ≤ eighth := by
  change eigA coupling s * cycleEigen rest s ≤ eighth
  have hedge : eigA coupling s ≤ eighth :=
    Q'.le_trans' _ _ _
      (gapEdge_dominates (by decide) (by decide) hs)
      (Q'.le_of_eqv (by decide : eigA coupling 1 ≈ eighth))
  have hm := Q'.mul_le_mul_of_nonneg hedge (cycleEigen_le_one_all rest s)
    (by decide : (0 : Q') ≤ eighth) (cycleEigen_nonneg_all rest s)
  exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.mul_one_eqv eighth))

/-! ## The squared-transfer spectral model -/

/-- The removed vacuum label has eigenvalue zero; every surviving common
irrep label has the square of the exact nonempty-cycle eigenvalue. -/
def projectedCycleSquaredEigen (l : Nat) (rest : List Nat) : Nat → Q'
  | 0 => 0
  | s + 1 =>
      cycleEigen (l :: rest) (s + 1) * cycleEigen (l :: rest) (s + 1)

/-- Exact positive spectral weight of the globally projected cycle packet. -/
def projectedCycleWeight (f : Nat → Q') (s : Nat) : Q' :=
  globalVacuumProject f s * globalVacuumProject f s

theorem projectedCycleSquaredEigen_nonneg (l : Nat) (rest : List Nat)
    (s : Nat) : (0 : Q') ≤ projectedCycleSquaredEigen l rest s := by
  cases s with
  | zero => exact Q'.le_refl' 0
  | succ s =>
      exact YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
        (cycleEigen (l :: rest) (s + 1))

theorem projectedCycleWeight_nonneg (f : Nat → Q') (s : Nat) :
    (0 : Q') ≤ projectedCycleWeight f s :=
  YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
    (globalVacuumProject f s)

/-- Uniform squared spectral edge for every nonempty bivalent cycle. -/
theorem projectedCycleSquaredEigen_le_sep (l : Nat) (rest : List Nat)
    (s : Nat) :
    projectedCycleSquaredEigen l rest s ≤ eighth * eighth := by
  cases s with
  | zero =>
      exact Q'.mul_nonneg eighth eighth (by decide) (by decide)
  | succ s =>
      let a := cycleEigen (l :: rest) (s + 1)
      have ha : (0 : Q') ≤ a := cycleEigen_nonneg_all (l :: rest) (s + 1)
      have hae : a ≤ eighth :=
        cycleEigen_excited_le_eighth_all l rest (by omega)
      have h1 : a * a ≤ eighth * a :=
        Q'.mul_le_mul_of_nonneg_right a eighth a hae ha
      have h2 : eighth * a ≤ eighth * eighth :=
        Q'.mul_le_mul_of_nonneg_left a eighth eighth hae (by decide)
      exact Q'.le_trans' _ _ _ h1 h2

/-- The finite positive spectral model of the squared cycle transfer. -/
def projectedCycleSpectralModel (f : Nat → Q')
    (l : Nat) (rest : List Nat) (N : Nat) : SpectralModel :=
  diagOp.toSpectralModel
    (projectedCycleSquaredEigen l rest) (projectedCycleWeight f) N
    (projectedCycleWeight_nonneg f)
    (projectedCycleSquaredEigen_nonneg l rest)

/-- The concrete finite self-adjoint operator realizing the cycle spectrum. -/
def projectedCycleSquaredOp (l : Nat) (rest : List Nat) (N : Nat) :
    FiniteOp :=
  diagOp (projectedCycleSquaredEigen l rest) N

theorem projectedCycleModel_lam_is_eigen (f : Nat → Q')
    (l : Nat) (rest : List Nat) (N i : Nat) (hi : i < N) :
    ((projectedCycleSpectralModel f l rest N).lam i) ≈
      ((projectedCycleSquaredOp l rest N).apply (basis i) i) :=
  Q'.eqv_symm (diagOp_eigen (projectedCycleSquaredEigen l rest) N i hi)

/-! ## Elimination-order compatibility -/

/-- Permuting the link-elimination order does not change any squared
nonvacuum eigenvalue of the realized operator. -/
theorem projectedCycleSquaredEigen_order_independent
    {l l' : Nat} {rest rest' : List Nat}
    (h : (l :: rest).Perm (l' :: rest')) (s : Nat) :
    projectedCycleSquaredEigen l rest s ≈
      projectedCycleSquaredEigen l' rest' s := by
  cases s with
  | zero => exact Q'.eqv_refl 0
  | succ s =>
      exact q_mul_congr
        (cycleEigen_order_independent h (s + 1))
        (cycleEigen_order_independent h (s + 1))

private theorem q_pow_eqv_congr {a b : Q'} (h : a ≈ b) :
    ∀ n : Nat, a ^ n ≈ b ^ n
  | 0 => by
      rw [Q'.pow_zero, Q'.pow_zero]
      exact Q'.eqv_refl 1
  | n + 1 => by
      rw [Q'.pow_succ, Q'.pow_succ]
      exact q_mul_congr h (q_pow_eqv_congr h n)

/-- Every finite-time correlator of the concrete cycle operator is independent
of the order in which the shared links are eliminated. -/
theorem projectedCycle_corr_order_independent (f : Nat → Q')
    {l l' : Nat} {rest rest' : List Nat}
    (h : (l :: rest).Perm (l' :: rest')) (N n : Nat) :
    corr (projectedCycleSpectralModel f l rest N) n ≈
      corr (projectedCycleSpectralModel f l' rest' N) n := by
  unfold corr projectedCycleSpectralModel
  exact SpectralGap.finSum_eqv_of_termwise _ _ (fun s =>
    Q'.mul_eqv_congr_left (projectedCycleWeight f s) _ _
      (q_pow_eqv_congr
        (projectedCycleSquaredEigen_order_independent h s) n)) N

/-! ## Same-state correlator identification -/

/-- Time zero is literally the globally projected common-label norm. -/
theorem projectedCycle_corr_zero_eq_norm (f : Nat → Q')
    (l : Nat) (rest : List Nat) (N : Nat) :
    corr (projectedCycleSpectralModel f l rest N) 0 ≈
      modeNorm (globalVacuumProject f) N := by
  refine Q'.eqv_trans _ _ _
    (corr_zero (projectedCycleSpectralModel f l rest N)) ?_
  unfold modeNorm projectedCycleSpectralModel projectedCycleWeight
  rw [YMGap.Continuum.MovingCutoff.fsum_eq_finSum]
  exact Q'.eqv_refl _

/-- Time one is literally the squared norm after applying the exact cycle
transfer to the same globally projected state on both sides. -/
theorem projectedCycle_corr_one_eq_transferred_norm (f : Nat → Q')
    (l : Nat) (rest : List Nat) (N : Nat) :
    corr (projectedCycleSpectralModel f l rest N) 1 ≈
      modeNorm (cycleTransfer (l :: rest) (globalVacuumProject f)) N := by
  unfold corr modeNorm projectedCycleSpectralModel
  rw [YMGap.Continuum.MovingCutoff.fsum_eq_finSum]
  change finSum (fun s =>
      projectedCycleWeight f s * projectedCycleSquaredEigen l rest s ^ 1) N ≈
    finSum (fun s =>
      cycleTransfer (l :: rest) (globalVacuumProject f) s *
        cycleTransfer (l :: rest) (globalVacuumProject f) s) N
  exact SpectralGap.finSum_eqv_of_termwise _ _ (fun s => by
    cases s with
    | zero =>
        unfold projectedCycleWeight projectedCycleSquaredEigen cycleTransfer
          globalVacuumProject
        rw [Q'.pow_succ, Q'.pow_zero]
        change ((0 : Q') * 0) * (0 * 1) ≈
          (cycleEigen (l :: rest) 0 * 0) *
            (cycleEigen (l :: rest) 0 * 0)
        refine Q'.eqv_trans _ 0 _ ?_ (Q'.eqv_symm ?_)
        · exact Q'.eqv_trans _ _ _
            (q_mul_congr (Q'.zero_mul_eqv 0) (Q'.zero_mul_eqv 1))
            (Q'.zero_mul_eqv 0)
        · exact Q'.eqv_trans _ _ _
            (q_mul_congr (Q'.mul_zero_eqv _) (Q'.mul_zero_eqv _))
            (Q'.zero_mul_eqv 0)
    | succ s =>
        unfold projectedCycleWeight projectedCycleSquaredEigen cycleTransfer
          globalVacuumProject
        rw [Q'.pow_succ, Q'.pow_zero]
        ring_qeqv) N

/-! ## Located separator and exact margin -/

/-- The shared-cycle squared separator, exactly `(1/8)^2 = 1/64`. -/
def projectedCycleSquaredSep : Q' := eighth * eighth

theorem projectedCycleSquaredSep_exact :
    projectedCycleSquaredSep ≈ Q'.mkPos 1 64 (by decide) := by decide

theorem projectedCycleSquaredSep_lt_one :
    projectedCycleSquaredSep < (1 : Q') := by decide

/-- A located spectral gap for the concrete finite shared-cycle operator,
uniform in cycle length, packet coefficients, and cutoff. -/
def projectedCycleLocatedGap (f : Nat → Q')
    (l : Nat) (rest : List Nat) (N : Nat) :
    LocatedSpectralGap (projectedCycleSpectralModel f l rest N) :=
  diagLocatedGap
    (projectedCycleSquaredEigen l rest) (projectedCycleWeight f) N
    (projectedCycleWeight_nonneg f)
    (projectedCycleSquaredEigen_nonneg l rest)
    projectedCycleSquaredSep projectedCycleSquaredSep_lt_one
    (projectedCycleSquaredEigen_le_sep l rest)

theorem projectedCycle_gapMargin_pos (f : Nat → Q')
    (l : Nat) (rest : List Nat) (N : Nat) :
    (0 : Q') < (projectedCycleLocatedGap f l rest N).gapMargin :=
  (projectedCycleLocatedGap f l rest N).gapMargin_pos

theorem projectedCycle_gapMargin_exact (f : Nat → Q')
    (l : Nat) (rest : List Nat) (N : Nat) :
    (projectedCycleLocatedGap f l rest N).gapMargin ≈
      Q'.mkPos 63 64 (by decide) := by
  change (1 - projectedCycleSquaredSep) ≈ Q'.mkPos 63 64 (by decide)
  decide

/-- The located-spectrum decay theorem is the already-derived uniform cycle
contraction when evaluated at one transfer step. -/
theorem projectedCycle_same_state_contraction_from_spectrum
    (f : Nat → Q') (l : Nat) (rest : List Nat) (N : Nat) :
    modeNorm (cycleTransfer (l :: rest) (globalVacuumProject f)) N ≤
      projectedCycleSquaredSep * modeNorm (globalVacuumProject f) N := by
  have hdec := (projectedCycleLocatedGap f l rest N).decay 1
  have hleft := projectedCycle_corr_one_eq_transferred_norm f l rest N
  have hzero := projectedCycle_corr_zero_eq_norm f l rest N
  rw [Q'.pow_succ, Q'.pow_zero] at hdec
  have hpow : projectedCycleSquaredSep * (1 : Q') ≈
      projectedCycleSquaredSep := Q'.mul_one_eqv _
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) <|
    Q'.le_trans' _ _ _ hdec <|
      Q'.le_of_eqv (by
        refine Q'.eqv_trans _
          (corr (projectedCycleSpectralModel f l rest N) 0 *
            projectedCycleSquaredSep) _ ?_ ?_
        · exact Q'.mul_eqv_congr_left _ _ _ hpow
        · refine Q'.eqv_trans _
            (modeNorm (globalVacuumProject f) N * projectedCycleSquaredSep) _
            (Q'.mul_eqv_congr_right _ _ _ hzero) ?_
          exact Q'.mul_comm_eqv _ _)

/-! ## Non-vacuity: the exact projected bigon -/

/-- The previously constructed two-link shared bigon, now regarded as the
concrete three-channel spectral model of this file. -/
def bigonProjectedSpectralModel : SpectralModel :=
  projectedCycleSpectralModel bigonGaugePacket 0 [1] 3

/-- The model has nonzero time-zero norm: the surviving quadratic loop has
unit Haar norm. -/
theorem bigonProjected_corr_zero_exact :
    corr bigonProjectedSpectralModel 0 ≈ 1 := by
  refine Q'.eqv_trans _
    (modeNorm (globalVacuumProject bigonGaugePacket) 3) _
    (projectedCycle_corr_zero_eq_norm bigonGaugePacket 0 [1] 3) ?_
  exact bigon_projected_norm_exact

/-- Its time-one correlator is the exact fourth power of the quadratic
single-link eigenvalue, because the mode crosses both links on both sides of
the same-state form. -/
theorem bigonProjected_corr_one_exact :
    corr bigonProjectedSpectralModel 1 ≈
      (SU2SharedLinkFusionBlock.quadraticEigen *
          SU2SharedLinkFusionBlock.quadraticEigen) *
        (SU2SharedLinkFusionBlock.quadraticEigen *
          SU2SharedLinkFusionBlock.quadraticEigen) := by
  refine Q'.eqv_trans _
    (modeNorm
      (cycleTransfer bigonOrder (globalVacuumProject bigonGaugePacket)) 3) _
    (projectedCycle_corr_one_eq_transferred_norm
      bigonGaugePacket 0 [1] 3) ?_
  exact bigon_projected_transfer_norm_exact

end YMGap.Continuum.SU2GlobalVacuumCycleSpectralLocalization

#print axioms YMGap.Continuum.SU2GlobalVacuumCycleSpectralLocalization.cycleEigen_nonneg_all
#print axioms YMGap.Continuum.SU2GlobalVacuumCycleSpectralLocalization.cycleEigen_le_one_all
#print axioms YMGap.Continuum.SU2GlobalVacuumCycleSpectralLocalization.cycleEigen_excited_le_eighth_all
#print axioms YMGap.Continuum.SU2GlobalVacuumCycleSpectralLocalization.projectedCycleSquaredEigen_le_sep
#print axioms YMGap.Continuum.SU2GlobalVacuumCycleSpectralLocalization.projectedCycleModel_lam_is_eigen
#print axioms YMGap.Continuum.SU2GlobalVacuumCycleSpectralLocalization.projectedCycleSquaredEigen_order_independent
#print axioms YMGap.Continuum.SU2GlobalVacuumCycleSpectralLocalization.projectedCycle_corr_order_independent
#print axioms YMGap.Continuum.SU2GlobalVacuumCycleSpectralLocalization.projectedCycle_corr_zero_eq_norm
#print axioms YMGap.Continuum.SU2GlobalVacuumCycleSpectralLocalization.projectedCycle_corr_one_eq_transferred_norm
#print axioms YMGap.Continuum.SU2GlobalVacuumCycleSpectralLocalization.projectedCycleLocatedGap
#print axioms YMGap.Continuum.SU2GlobalVacuumCycleSpectralLocalization.projectedCycle_gapMargin_exact
#print axioms YMGap.Continuum.SU2GlobalVacuumCycleSpectralLocalization.projectedCycle_same_state_contraction_from_spectrum
#print axioms YMGap.Continuum.SU2GlobalVacuumCycleSpectralLocalization.bigonProjected_corr_zero_exact
#print axioms YMGap.Continuum.SU2GlobalVacuumCycleSpectralLocalization.bigonProjected_corr_one_exact
