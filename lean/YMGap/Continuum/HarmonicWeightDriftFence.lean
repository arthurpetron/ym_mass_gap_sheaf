/-
`HarmonicWeightDriftFence` identifies the exact coefficient drift between
consecutive harmonic weights and fences two over-strong mass-drift claims.

Writing `m=k+2`,

  harmW(k)   = (m-1)/m,
  harmW(k+1) = m/(m+1),

so the exact base multiplier is `m^2/(m^2-1)`.  Every character coefficient
therefore changes by this multiplier raised to its exact Casimir exponent.
This is the missing weight-drift term which is absent from same-weight theta
tail bounds.

The natural inverse-square *relative* mass claim is false already at `k=0`,
and the unit-coefficient inverse-square *additive* claim is false at `k=2`.
Thus an all-k proof must exploit quotient cancellation and, even additively,
needs a constant larger than one.  These are closed rational refutations, not
numerical measurements or new carriers.
-/

import YMGap.Continuum.HarmonicFusedSchurObstruction
import YMGap.Continuum.RefinedRetune

namespace YMGap.Continuum.HarmonicWeightDriftFence

set_option maxHeartbeats 800000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.AllWindowCorrDirichlet
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.CutoffCorrelationMonotone
open YMGap.Continuum.FusedOffDiagonalCompression
open YMGap.Continuum.FusedSchurSpacingBridge
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RefinedRetune
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

/-! ## 1. Exact harmonic base and coefficient drift -/

def driftDen (k : Nat) : Nat := (k + 2) * (k + 2) - 1

theorem driftDen_pos (k : Nat) : 0 < driftDen k := by
  unfold driftDen
  have h4 : 4 <= (k + 2) * (k + 2) :=
    Nat.mul_le_mul (by omega : 2 <= k + 2) (by omega : 2 <= k + 2)
  omega

/-- Exact consecutive harmonic base multiplier `m^2/(m^2-1)`. -/
def driftRatio (k : Nat) : Q' :=
  Q'.divPos (harmW (k + 1)) (harmW k) (harmW_pos k)

theorem driftRatio_pos (k : Nat) : (0 : Q') < driftRatio k := by
  unfold driftRatio Q'.divPos
  exact Q'.mul_pos (harmW_pos (k + 1)) (Q'.recipPos_pos _ _)

private theorem harmU_mul_den (k : Nat) :
    harmU k * Q'.ofNat (k + 2) ≈ (1 : Q') := by
  unfold harmU unit
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast, Int.mul_one, Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul]

private theorem harmW_mul_den (k : Nat) :
    harmW k * Q'.ofNat (k + 2) ≈ Q'.ofNat (k + 1) := by
  have hM : Q'.ofNat (k + 2) ≈ Q'.ofNat (k + 1) + (1 : Q') := by
    simpa [Nat.add_assoc] using Q'.ofNat_add_eqv (k + 1) 1
  unfold harmW oneSub
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 (-(harmU k)) (Q'.ofNat (k + 2))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.one_mul_eqv (Q'.ofNat (k + 2)))
      (Q'.neg_mul_eqv (harmU k) (Q'.ofNat (k + 2)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hM
      (Q'.neg_eqv_congr _ _ (harmU_mul_den k))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (Q'.ofNat (k + 1)) 1 (-1)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (Q'.ofNat (k + 1)) _ _
      (Q'.add_neg_self_eqv (1 : Q'))) ?_
  exact QPoly.q_add_zero_eqv _

private theorem driftDen_factor (k : Nat) :
    driftDen k = (k + 1) * (k + 3) := by
  unfold driftDen
  have hsq : (k + 2) * (k + 2) = k * k + 4 * k + 4 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    omega
  have hprod : (k + 1) * (k + 3) = k * k + 4 * k + 3 := by
    rw [Nat.add_mul, Nat.mul_add]
    omega
  rw [hsq, hprod]
  omega

/-- Cleared exact base identity.  This avoids any analytic approximation of
the harmonic change of variables. -/
theorem harmW_step_cleared (k : Nat) :
    harmW (k + 1) * Q'.ofNat (driftDen k) ≈
      harmW k * Q'.ofNat ((k + 2) * (k + 2)) := by
  rw [driftDen_factor]
  have hL : harmW (k + 1) * Q'.ofNat ((k + 1) * (k + 3)) ≈
      Q'.ofNat (k + 1) * Q'.ofNat (k + 2) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (harmW (k + 1)) _ _
        (HeatKernelRGStep.ofNat_mul_eqv (k + 1) (k + 3))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv
        (harmW (k + 1)) (Q'.ofNat (k + 1)) (Q'.ofNat (k + 3)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (Q'.ofNat (k + 3))
        (Q'.mul_comm_eqv (harmW (k + 1)) (Q'.ofNat (k + 1)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofNat (k + 1))
        (harmW (k + 1)) (Q'.ofNat (k + 3))) ?_
    exact Q'.mul_eqv_congr_left (Q'.ofNat (k + 1)) _ _
      (harmW_mul_den (k + 1))
  have hR : harmW k * Q'.ofNat ((k + 2) * (k + 2)) ≈
      Q'.ofNat (k + 1) * Q'.ofNat (k + 2) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (harmW k) _ _
        (HeatKernelRGStep.ofNat_mul_eqv (k + 2) (k + 2))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    exact Q'.mul_eqv_congr_right _ _ (Q'.ofNat (k + 2)) (harmW_mul_den k)
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)

/-- Consecutive harmonic weights differ by exactly `driftRatio`. -/
theorem harmW_step_eqv (k : Nat) :
    harmW (k + 1) ≈ harmW k * driftRatio k := by
  unfold driftRatio
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) ?_
  exact Q'.divPos_mul_eqv _ _ _

/-- Exact exponent-wise drift of every character coefficient. -/
theorem coeffW_harmonic_step (k s : Nat) :
    coeffW (harmW (k + 1)) s ≈
      coeffW (harmW k) s * qpow (driftRatio k) (c4 s) := by
  unfold coeffW
  have hb := qpow_eqv_congr_base (harmW_step_eqv k) (c4 s)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (dimQ s) _ _ hb) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (dimQ s) _ _ (qpow_mul_base (harmW k) (driftRatio k) (c4 s))) ?_
  ring_qeqv

/-- The squared theta summand carries twice the same exact Casimir drift. -/
theorem coeffSq_harmonic_step (k s : Nat) :
    coeffW (harmW (k + 1)) s * coeffW (harmW (k + 1)) s ≈
      (coeffW (harmW k) s * coeffW (harmW k) s) *
        (qpow (driftRatio k) (c4 s) * qpow (driftRatio k) (c4 s)) := by
  have h := coeffW_harmonic_step k s
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ h)
      (Q'.mul_eqv_congr_left _ _ _ h)) ?_
  ring_qeqv

/-! ## 2. Strict all-k harmonic mass blocks -/

/-- The universal boundary term in the exact Dirichlet identity gives the
strict lower bound `1/2 ≤ D-A`, independently of weight and cutoff. -/
theorem half_le_coordNormSq_sub_adjCorr (w : Q') (N : Nat) :
    Q'.mkPos 1 2 (by decide) <= coordNormSq w N - adjCorr w N := by
  let D := coordNormSq w N
  let A := adjCorr w N
  let b := coeffW w N * coeffW w N
  let e := dirichletEnergy w N
  have hb : (0 : Q') <= b := SumOfSquares.q_mul_self_nonneg _
  have he : (0 : Q') <= e := dirichletEnergy_nonneg _ _
  have hzero : coeffW w 0 * coeffW w 0 ≈ (1 : Q') := by
    rw [coeffW_zero]
    exact Q'.one_mul_eqv 1
  have hone : (1 : Q') <= coeffW w 0 * coeffW w 0 + b + e := by
    have hbase : (1 : Q') <= coeffW w 0 * coeffW w 0 :=
      Q'.le_of_eqv (Q'.eqv_symm hzero)
    have h1 : coeffW w 0 * coeffW w 0 <=
        coeffW w 0 * coeffW w 0 + b :=
      Q'.add_le_self_of_nonneg _ _ hb
    have h2 : coeffW w 0 * coeffW w 0 + b <=
        (coeffW w 0 * coeffW w 0 + b) + e :=
      Q'.add_le_self_of_nonneg _ _ he
    exact Q'.le_trans' _ _ _ hbase (Q'.le_trans' _ _ _ h1 h2)
  have hid := twice_norm_sub_corr_eq_boundary_dirichlet w N
  have hscaled : (1 : Q') <= Q'.ofNat 2 * (D - A) :=
    Q'.le_trans' _ _ _ hone (Q'.le_of_eqv (Q'.eqv_symm hid))
  have hmul : Q'.mkPos 1 2 (by decide) * Q'.ofNat 2 <=
      (D - A) * Q'.ofNat 2 := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (by decide :
        Q'.mkPos 1 2 (by decide) * Q'.ofNat 2 ≈ (1 : Q')))
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv (Q'.mul_comm_eqv (Q'.ofNat 2) (D - A))))
  exact BakryEmery.le_of_mul_le_mul_right_pos (by decide) hmul

theorem harmonicMass_pos_all (k : Nat) : (0 : Q') < harmonicMass k := by
  let diff := coordNormSq (harmW k) (Ncut k) - adjCorr (harmW k) (Ncut k)
  let D := coordNormSq (harmW k) (Ncut k)
  have hdiff : (0 : Q') < diff :=
    ClusteringImpliesGap.lt_of_lt_of_le
      (by decide : (0 : Q') < Q'.mkPos 1 2 (by decide))
      (half_le_coordNormSq_sub_adjCorr (harmW k) (Ncut k))
  have hratio : (0 : Q') < Q'.divPos diff D
      (coordNormSq_pos (harmW_nonneg k) (Ncut k)) :=
    Q'.mul_pos hdiff (Q'.recipPos_pos _ _)
  exact ClusteringImpliesGap.lt_of_lt_of_le hratio
    (Q'.ge_of_eqv (harmonicMass_eq_ratio k))

theorem harmonicShell_pos_all (k : Nat) : (0 : Q') < harmonicShell k := by
  unfold harmonicShell rot11
  exact Q'.add_pos
    (Q'.mul_pos (Q'.mul_pos (by decide) (by decide)) (harmonicMass_pos_all k))
    (Q'.mul_pos (Q'.mul_pos (by decide) (by decide))
      (harmonicMass_pos_all (k + 1)))

def harmonicErosionAll (k : Nat) : Q' :=
  shellLoss (harmonicCoupling k) (harmonicShell k) (harmonicShell_pos_all k)

def harmonicSchurAll (k : Nat) : Q' :=
  schurMass (harmonicHead k) (harmonicShell k) (harmonicCoupling k)
    (harmonicShell_pos_all k)

theorem harmonicErosionAll_nonneg (k : Nat) : (0 : Q') <= harmonicErosionAll k := by
  unfold harmonicErosionAll shellLoss Q'.divPos
  exact Q'.mul_nonneg _ _
    (SumOfSquares.q_mul_self_nonneg (harmonicCoupling k))
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

theorem harmonicCoupling_size_all (k : Nat) :
    harmonicCoupling k * harmonicCoupling k <=
      harmonicErosionAll k * harmonicShell k := by
  exact Q'.le_of_eqv
    (Q'.eqv_symm
      (Q'.divPos_mul_eqv
        (harmonicCoupling k * harmonicCoupling k)
        (harmonicShell k) (harmonicShell_pos_all k)))

/-- The actual harmonic Schur/spacing law is already unconditional on the
complete two-anchor prefix `k=0,1,2`.  These are precisely the scales whose
correlation quotient is covered by the existing `w≤3/4` certificate. -/
theorem harmonicSchur_spacing_initial_three {k : Nat} (hk : k <= 2) :
    harmonicSchurAll k * harmonicSpacing (k + 1) <=
      harmonicMass (k + 1) * harmonicSpacing k := by
  have cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases cases with rfl | rfl | rfl <;> decide

/-- Consequently the full coupled operator/spacing cross law holds for the
same actual harmonic prefix, with its exact Schur erosion. -/
theorem harmonic_operator_spacing_initial_three {k : Nat} (hk : k <= 2) :
    harmonicHead k * harmonicSpacing (k + 1) <=
      (harmonicErosionAll k + harmonicMass (k + 1)) * harmonicSpacing k := by
  exact spacing_cross_of_schur (harmonicShell_pos_all k)
    (harmonicErosionAll_nonneg k)
    (Q'.le_of_lt (harmonicSpacing_pos (k + 1)))
    (harmonicSpacing_contracts k)
    (harmonicCoupling_size_all k)
    (harmonicSchur_spacing_initial_three hk)

/-! ## 3. Kernel fences for over-strong summable drift claims -/

/-- **Relative inverse-square drift is false.**  Already at the first actual
harmonic pair, retaining the factor `1-1/(k+2)^2` is too optimistic.  The
relative change is first-order harmonic, even though its additive size can be
inverse-square because the mass itself is harmonic-sized. -/
theorem inverse_square_relative_mass_drift_fails_at_zero :
    not (((1 : Q') - invSqTerm 2 (by decide) 0) * harmonicMass 0 <=
      harmonicMass 1) := by
  decide

/-- The same relative inverse-square proposal also fails at the next scale;
the first fence is not an isolated small-cutoff accident. -/
theorem inverse_square_relative_mass_drift_fails_at_one :
    not (((1 : Q') - invSqTerm 2 (by decide) 1) * harmonicMass 1 <=
      harmonicMass 2) := by
  decide

/-- **Unit additive constant is also false.**  The summable shape is viable
only with a larger derived constant: at `k=2`, the actual mass drop exceeds
`1/(k+2)^2`. -/
theorem unit_inverse_square_additive_mass_drift_fails_at_two :
    not (harmonicMass 2 - harmonicMass 3 <=
      invSqTerm 2 (by decide) 2) := by
  decide

/-- Exact positive evidence for the next viable target: coefficient two pays
the additive inverse-square drop through the first four harmonic transitions.
This finite statement is a scouting fence only; it is not presented as an
all-k theorem. -/
theorem two_inverse_square_additive_prefix :
    (harmonicMass 0 - harmonicMass 1 <=
        Q'.ofNat 2 * invSqTerm 2 (by decide) 0) /\
    (harmonicMass 1 - harmonicMass 2 <=
        Q'.ofNat 2 * invSqTerm 2 (by decide) 1) /\
    (harmonicMass 2 - harmonicMass 3 <=
        Q'.ofNat 2 * invSqTerm 2 (by decide) 2) /\
    (harmonicMass 3 - harmonicMass 4 <=
        Q'.ofNat 2 * invSqTerm 2 (by decide) 3) := by
  decide

end YMGap.Continuum.HarmonicWeightDriftFence

#print axioms YMGap.Continuum.HarmonicWeightDriftFence.driftDen_pos
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.driftRatio_pos
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.harmW_step_cleared
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.harmW_step_eqv
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.coeffW_harmonic_step
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.coeffSq_harmonic_step
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.half_le_coordNormSq_sub_adjCorr
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.harmonicMass_pos_all
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.harmonicShell_pos_all
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.harmonicCoupling_size_all
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.harmonicSchur_spacing_initial_three
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.harmonic_operator_spacing_initial_three
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.inverse_square_relative_mass_drift_fails_at_zero
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.inverse_square_relative_mass_drift_fails_at_one
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.unit_inverse_square_additive_mass_drift_fails_at_two
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.two_inverse_square_additive_prefix
