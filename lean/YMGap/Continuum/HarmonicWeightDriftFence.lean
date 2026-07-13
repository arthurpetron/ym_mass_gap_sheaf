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

/-! ## 3. Exact quotient-cancellation recurrence -/

def harmonicD (k : Nat) : Q' := coordNormSq (harmW k) (Ncut k)
def harmonicA (k : Nat) : Q' := adjCorr (harmW k) (Ncut k)

theorem harmonicD_pos (k : Nat) : (0 : Q') < harmonicD k :=
  coordNormSq_pos (harmW_nonneg k) (Ncut k)

/-- The division-free numerator of the consecutive mass drop. -/
def harmonicMassCross (k : Nat) : Q' :=
  harmonicA (k + 1) * harmonicD k - harmonicA k * harmonicD (k + 1)

theorem harmonicMass_eq_DA (k : Nat) :
    harmonicMass k ≈ Q'.divPos (harmonicD k - harmonicA k)
      (harmonicD k) (harmonicD_pos k) := by
  exact harmonicMass_eq_ratio k

private theorem harmonicMass_mul_D (k : Nat) :
    harmonicMass k * harmonicD k ≈ harmonicD k - harmonicA k := by
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (harmonicD k) (harmonicMass_eq_DA k))
    (Q'.divPos_mul_eqv _ _ _)

private theorem quotient_cross_cancel (D0 A0 D1 A1 : Q') :
    (D0 - A0) * D1 + -((D1 - A1) * D0) ≈
      A1 * D0 + -(A0 * D1) := by
  have hleft : (D0 - A0) * D1 ≈ D0 * D1 + -(A0 * D1) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv D0 (-A0) D1) ?_
    exact Q'.add_eqv_congr_left _ _ _ (Q'.neg_mul_eqv A0 D1)
  have hright : -((D1 - A1) * D0) ≈ -(D1 * D0) + A1 * D0 := by
    refine Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.add_mul_eqv D1 (-A1) D0)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (D1 * D0) ((-A1) * D0)) ?_
    refine Q'.add_eqv_congr_left (-(D1 * D0)) _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.neg_mul_eqv A1 D0)) ?_
    exact Q'.neg_neg_eqv (A1 * D0)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hleft hright) ?_
  refine Q'.eqv_trans _ _ _
    (q_interchange (D0 * D1) (-(A0 * D1)) (-(D1 * D0)) (A1 * D0)) ?_
  have hcancel : D0 * D1 + -(D1 * D0) ≈ (0 : Q') := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (D0 * D1) _ _
        (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv D1 D0))) ?_
    exact Q'.add_neg_self_eqv (D0 * D1)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ hcancel) ?_
  refine Q'.eqv_trans _ _ _ (q_zero_add_eqv _) ?_
  exact Q'.add_comm_eqv (-(A0 * D1)) (A1 * D0)

/-- **Exact inter-scale recurrence.**  The full harmonic mass drop is the
cross determinant `A_{k+1}D_k-A_kD_{k+1}` divided by the two positive
normalizers.  Both weight drift and cutoff drift occur only inside this
single numerator, where their leading normalizer growth can cancel. -/
theorem harmonicMass_drop_eq_cross (k : Nat) :
    harmonicMass k - harmonicMass (k + 1) ≈
      Q'.divPos (harmonicMassCross k)
        (harmonicD k * harmonicD (k + 1))
        (Q'.mul_pos (harmonicD_pos k) (harmonicD_pos (k + 1))) := by
  let x := harmonicMass k - harmonicMass (k + 1)
  let den := harmonicD k * harmonicD (k + 1)
  let cross := harmonicMassCross k
  have hden : (0 : Q') < den := Q'.mul_pos (harmonicD_pos k) (harmonicD_pos (k + 1))
  have h0 := harmonicMass_mul_D k
  have h1 := harmonicMass_mul_D (k + 1)
  have hx : x * den ≈ cross := by
    unfold x den cross harmonicMassCross
    refine Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv (harmonicMass k) (-(harmonicMass (k + 1)))
        (harmonicD k * harmonicD (k + 1))) ?_
    have hx0 : harmonicMass k * (harmonicD k * harmonicD (k + 1)) ≈
        (harmonicD k - harmonicA k) * harmonicD (k + 1) := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv
          (harmonicMass k) (harmonicD k) (harmonicD (k + 1)))) ?_
      exact Q'.mul_eqv_congr_right _ _ (harmonicD (k + 1)) h0
    have hx1 : -(harmonicMass (k + 1)) *
          (harmonicD k * harmonicD (k + 1)) ≈
        -((harmonicD (k + 1) - harmonicA (k + 1)) * harmonicD k) := by
      refine Q'.eqv_trans _ _ _
        (Q'.neg_mul_eqv (harmonicMass (k + 1))
          (harmonicD k * harmonicD (k + 1))) ?_
      apply Q'.neg_eqv_congr
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (harmonicMass (k + 1)) _ _
          (Q'.mul_comm_eqv (harmonicD k) (harmonicD (k + 1)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv
          (harmonicMass (k + 1)) (harmonicD (k + 1)) (harmonicD k))) ?_
      exact Q'.mul_eqv_congr_right _ _ (harmonicD k) h1
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hx0 hx1) ?_
    exact quotient_cross_cancel
      (harmonicD k) (harmonicA k) (harmonicD (k + 1)) (harmonicA (k + 1))
  have hy : (Q'.divPos cross den hden) * den ≈ cross :=
    Q'.divPos_mul_eqv cross den hden
  apply Q'.mul_left_cancel_of_pos hden
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv den x) ?_
  refine Q'.eqv_trans _ _ _ hx ?_
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv den (Q'.divPos cross den hden)) hy)

/-- A division-free determinant estimate with coefficient two is exactly
enough for the desired summable additive mass drift. -/
theorem harmonicMass_drop_le_two_invSq_of_cross (k : Nat)
    (hcross : harmonicMassCross k <=
      (Q'.ofNat 2 * invSqTerm 2 (by decide) k) *
        (harmonicD k * harmonicD (k + 1))) :
    harmonicMass k - harmonicMass (k + 1) <=
      Q'.ofNat 2 * invSqTerm 2 (by decide) k := by
  have hq := Q'.divPos_le_of_le_mul
    (harmonicMassCross k)
    (harmonicD k * harmonicD (k + 1))
    (Q'.mul_pos (harmonicD_pos k) (harmonicD_pos (k + 1))) hcross
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (harmonicMass_drop_eq_cross k)) hq

/-! ## 4. Exact separation of weight drift and cutoff drift -/

/-- The intermediate diagonal normalizer after changing the harmonic weight,
but before enlarging the quadratic cutoff. -/
def harmonicMidD (k : Nat) : Q' :=
  coordNormSq (harmW (k + 1)) (Ncut k)

/-- The corresponding intermediate adjacent numerator. -/
def harmonicMidA (k : Nat) : Q' :=
  adjCorr (harmW (k + 1)) (Ncut k)

/-- The determinant contribution of the exact per-mode weight drift at the
old cutoff. -/
def harmonicWeightCross (k : Nat) : Q' :=
  harmonicMidA k * harmonicD k - harmonicA k * harmonicMidD k

/-- The remaining determinant contribution from adding the shell
`Ncut k < s ≤ Ncut (k+1)` at the new weight.  The diagonal shell enters with
the favorable negative sign and must not be discarded until after the
weight-drift cancellation has been exposed. -/
def harmonicCutoffCross (k : Nat) : Q' :=
  (harmonicA (k + 1) - harmonicMidA k) * harmonicD k -
    harmonicA k * (harmonicD (k + 1) - harmonicMidD k)

private theorem cross_weight_cutoff_split
    (D0 A0 Dm Am D1 A1 : Q') :
    A1 * D0 + -(A0 * D1) ≈
      (Am * D0 + -(A0 * Dm)) +
        ((A1 + -Am) * D0 + -(A0 * (D1 + -Dm))) := by
  let X := Am * D0
  let Y := A0 * Dm
  let U := A1 * D0
  let V := A0 * D1
  have hcutL : (A1 + -Am) * D0 ≈ U + -X := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv A1 (-Am) D0) ?_
    exact Q'.add_eqv_congr_left U _ _ (Q'.neg_mul_eqv Am D0)
  have hcutR : -(A0 * (D1 + -Dm)) ≈ -V + Y := by
    refine Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.mul_add_eqv A0 D1 (-Dm))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv V (A0 * (-Dm))) ?_
    refine Q'.add_eqv_congr_left (-V) _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv A0 Dm)) ?_
    exact Q'.neg_neg_eqv Y
  have hadd (X Y U V : Q') :
      U + -V ≈ (X + -Y) + ((U + -X) + (-V + Y)) := by
    have hreorder :
        (X + -Y) + ((U + -X) + (-V + Y)) ≈
          (X + -X) + ((-Y + Y) + (U + -V)) := by
      ring_qeqv
    refine Q'.eqv_symm (Q'.eqv_trans _ _ _ hreorder ?_)
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.add_neg_self_eqv X)
        (Q'.add_eqv_congr_left (-Y + Y) _ _ (Q'.eqv_refl _))) ?_
    refine Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv _) ?_
    have hy : -Y + Y ≈ (0 : Q') := by
      refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (-Y) Y) ?_
      exact Q'.add_neg_self_eqv Y
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (U + -V) hy) ?_
    exact QPoly.q_zero_add_eqv (U + -V)
  refine Q'.eqv_trans _ _ _ (hadd X Y U V) ?_
  exact Q'.add_eqv_congr_left (X + -Y) _ _
    (Q'.add_eqv_congr' (Q'.eqv_symm hcutL) (Q'.eqv_symm hcutR))

/-- **Exact two-stage determinant recurrence.**  This is the cancellation-
preserving form of the consecutive harmonic mass numerator: first drift every
retained mode by its exact `driftRatio`, then add the new cutoff shell. -/
theorem harmonicMassCross_eq_weight_add_cutoff (k : Nat) :
    harmonicMassCross k ≈ harmonicWeightCross k + harmonicCutoffCross k := by
  unfold harmonicMassCross harmonicWeightCross harmonicCutoffCross
  exact cross_weight_cutoff_split
    (harmonicD k) (harmonicA k) (harmonicMidD k) (harmonicMidA k)
    (harmonicD (k + 1)) (harmonicA (k + 1))

theorem harmonicMidD_le_next (k : Nat) :
    harmonicMidD k ≤ harmonicD (k + 1) := by
  have hN : Ncut k + 1 ≤ Ncut (k + 1) + 1 := by
    apply Nat.add_le_add_right
    unfold Ncut
    exact Nat.mul_le_mul (by omega) (by omega)
  unfold harmonicMidD harmonicD coordNormSq
  exact AFRateCalibration.fsum_le_of_le
    (fun i => Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg (k + 1)) i)
      (coeffW_nonneg (harmW_nonneg (k + 1)) i)) hN

theorem harmonicMidA_le_next (k : Nat) :
    harmonicMidA k ≤ harmonicA (k + 1) := by
  have hN : Ncut k ≤ Ncut (k + 1) := by
    unfold Ncut
    exact Nat.mul_le_mul (by omega) (by omega)
  unfold harmonicMidA harmonicA adjCorr
  exact AFRateCalibration.fsum_le_of_le
    (fun i => Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg (k + 1)) i)
      (coeffW_nonneg (harmW_nonneg (k + 1)) (i + 1))) hN

/-- Once the exact split has been made, only the cutoff part may be bounded
one-sidedly: its diagonal-shell term is nonpositive.  This leaves the difficult
weight covariance intact instead of separately bounding numerator and
denominator growth. -/
theorem harmonicCutoffCross_le_adjShell_mul_D (k : Nat) :
    harmonicCutoffCross k ≤
      (harmonicA (k + 1) - harmonicMidA k) * harmonicD k := by
  let X := (harmonicA (k + 1) - harmonicMidA k) * harmonicD k
  let Y := harmonicA k * (harmonicD (k + 1) - harmonicMidD k)
  have hY : (0 : Q') ≤ Y := by
    unfold Y
    exact Q'.mul_nonneg _ _
      (adjCorr_nonneg (harmW_nonneg k) (Ncut k))
      (Q'.sub_nonneg_of_le (harmonicMidD_le_next k))
  have hneg : -Y ≤ (0 : Q') := by
    have h := FusionCoreStepRoundE.q_add_neg_nonpos hY
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (QPoly.q_zero_add_eqv (-Y))) h
  have hadd := Q'.add_le_add_left X (-Y) 0 hneg
  change X + -Y ≤ X
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (QPoly.q_add_zero_eqv _))

/-- The genuine same-weight cutoff determinant, comparing the old and new
cutoffs after the weight has already been changed. -/
def harmonicPureCutoffCross (k : Nat) : Q' :=
  harmonicA (k + 1) * harmonicMidD k -
    harmonicMidA k * harmonicD (k + 1)

private theorem determinant_cocycle
    (D0 A0 Dm Am D1 A1 : Q') :
    (A1 * D0 + -(A0 * D1)) * Dm ≈
      (Am * D0 + -(A0 * Dm)) * D1 +
        (A1 * Dm + -(Am * D1)) * D0 := by
  let U := (A1 * D0) * Dm
  let V := (A0 * D1) * Dm
  let W := (Am * D0) * D1
  have swap_last (a b c : Q') : (a * b) * c ≈ (a * c) * b := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b c) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left a _ _ (Q'.mul_comm_eqv b c)) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv a c b)
  have hL : (A1 * D0 + -(A0 * D1)) * Dm ≈ U + -V := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv (A1 * D0) (-(A0 * D1)) Dm) ?_
    exact Q'.add_eqv_congr_left U _ _ (Q'.neg_mul_eqv (A0 * D1) Dm)
  have hR0 : (Am * D0 + -(A0 * Dm)) * D1 ≈ W + -V := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv (Am * D0) (-(A0 * Dm)) D1) ?_
    refine Q'.add_eqv_congr_left W _ _ ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv (A0 * Dm) D1) ?_
    apply Q'.neg_eqv_congr
    exact swap_last A0 Dm D1
  have hR1 : (A1 * Dm + -(Am * D1)) * D0 ≈ U + -W := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv (A1 * Dm) (-(Am * D1)) D0) ?_
    refine Q'.add_eqv_congr' ?_ ?_
    · exact swap_last A1 Dm D0
    · refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv (Am * D1) D0) ?_
      apply Q'.neg_eqv_congr
      exact swap_last Am D1 D0
  have hcancel : (W + -V) + (U + -W) ≈ U + -V := by
    have hreorder : (W + -V) + (U + -W) ≈
        (W + -W) + (U + -V) := by
      ring_qeqv
    refine Q'.eqv_trans _ _ _ hreorder ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (U + -V) (Q'.add_neg_self_eqv W)) ?_
    exact QPoly.q_zero_add_eqv (U + -V)
  refine Q'.eqv_trans _ _ _ hL ?_
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hR0 hR1) hcancel)

/-- **Cancellation-preserving barycentric recurrence.**  Multiplication by
the positive intermediate normalizer produces an exact sum of two genuine
two-point determinants: one from changing the weight at fixed cutoff, and one
from changing the cutoff at fixed new weight.  No numerator or denominator
growth is bounded separately. -/
theorem harmonicMassCross_mul_midD_eq (k : Nat) :
    harmonicMassCross k * harmonicMidD k ≈
      harmonicWeightCross k * harmonicD (k + 1) +
        harmonicPureCutoffCross k * harmonicD k := by
  unfold harmonicMassCross harmonicWeightCross harmonicPureCutoffCross
  exact determinant_cocycle
    (harmonicD k) (harmonicA k) (harmonicMidD k) (harmonicMidA k)
    (harmonicD (k + 1)) (harmonicA (k + 1))

/-- The pure cutoff determinant has the favorable sign: at a fixed positive
weight, enlarging the retained block increases `A/D`. -/
theorem harmonicPureCutoffCross_nonneg (k : Nat) :
    (0 : Q') ≤ harmonicPureCutoffCross k := by
  have hN : Ncut k ≤ Ncut (k + 1) := by
    unfold Ncut
    exact Nat.mul_le_mul (by omega) (by omega)
  let M := Ncut (k + 1) - Ncut k
  have hNM : Ncut k + M = Ncut (k + 1) := Nat.add_sub_of_le hN
  have h := finite_cutoff_tail_compare
    (harmW_nonneg (k + 1)) (harmW_le_one (k + 1))
    (harmW_pos (k + 1)) (Ncut k) M
  rw [hNM] at h
  unfold harmonicPureCutoffCross harmonicMidA harmonicMidD harmonicA harmonicD
  exact Q'.sub_nonneg_of_le h

/-! ## 5. The exact weight-drift covariance -/

def driftSqFactor (k s : Nat) : Q' :=
  qpow (driftRatio k) (c4 s) * qpow (driftRatio k) (c4 s)

def driftAdjFactor (k s : Nat) : Q' :=
  qpow (driftRatio k) (c4 s) * qpow (driftRatio k) (c4 (s + 1))

def harmonicDriftD (k : Nat) : Q' :=
  fsum (fun s =>
    (coeffW (harmW k) s * coeffW (harmW k) s) * driftSqFactor k s)
    (Ncut k + 1)

def harmonicDriftA (k : Nat) : Q' :=
  fsum (fun s =>
    (coeffW (harmW k) s * coeffW (harmW k) (s + 1)) *
      driftAdjFactor k s) (Ncut k)

theorem harmonicMidD_eq_driftSum (k : Nat) :
    harmonicMidD k ≈ harmonicDriftD k := by
  unfold harmonicMidD harmonicDriftD coordNormSq
  exact CubeRatioBounds.fsum_eqv_congr _ _
    (fun s => coeffSq_harmonic_step k s) (Ncut k + 1)

private theorem coeffAdj_harmonic_step (k s : Nat) :
    coeffW (harmW (k + 1)) s * coeffW (harmW (k + 1)) (s + 1) ≈
      (coeffW (harmW k) s * coeffW (harmW k) (s + 1)) *
        driftAdjFactor k s := by
  have h0 := coeffW_harmonic_step k s
  have h1 := coeffW_harmonic_step k (s + 1)
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ h0)
      (Q'.mul_eqv_congr_left _ _ _ h1)) ?_
  unfold driftAdjFactor
  ring_qeqv

theorem harmonicMidA_eq_driftSum (k : Nat) :
    harmonicMidA k ≈ harmonicDriftA k := by
  unfold harmonicMidA harmonicDriftA adjCorr
  exact CubeRatioBounds.fsum_eqv_congr _ _
    (fun s => coeffAdj_harmonic_step k s) (Ncut k)

/-- The fixed-cutoff determinant is exactly a covariance between adjacent and
diagonal modes under two different Casimir drift factors. -/
theorem harmonicWeightCross_eq_driftCovariance (k : Nat) :
    harmonicWeightCross k ≈
      harmonicDriftA k * harmonicD k - harmonicA k * harmonicDriftD k := by
  unfold harmonicWeightCross
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ (harmonicD k) (harmonicMidA_eq_driftSum k))
    (Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_left (harmonicA k) _ _ (harmonicMidD_eq_driftSum k)))

/-- The covariance cannot be bounded by a uniform termwise ordering: at the
first uncovered scale, the adjacent drift of mode one exceeds the diagonal
drift of mode zero. -/
theorem no_adj_le_sq_drift_order_at_k3 :
    not (driftAdjFactor 3 1 ≤ driftSqFactor 3 0) := by
  unfold driftAdjFactor driftSqFactor driftRatio harmW harmU
    ReciprocalBernoulliUpper.oneSub unit c4 Q'.divPos Q'.recipPos qpow
  decide

/-- The opposite uniform ordering fails simultaneously: the diagonal drift
of mode one exceeds the adjacent drift of mode zero.  Hence a valid proof of
the coefficient-two determinant bound must antisymmetrize the double sum; no
one-direction per-mode comparison can close it. -/
theorem no_sq_le_adj_drift_order_at_k3 :
    not (driftSqFactor 3 1 ≤ driftAdjFactor 3 0) := by
  unfold driftAdjFactor driftSqFactor driftRatio harmW harmU
    ReciprocalBernoulliUpper.oneSub unit c4 Q'.divPos Q'.recipPos qpow
  decide

/-! ## 6. Kernel fences for over-strong summable drift claims -/

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
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.harmonicMass_drop_eq_cross
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.harmonicMass_drop_le_two_invSq_of_cross
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.harmonicMassCross_eq_weight_add_cutoff
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.harmonicMidD_le_next
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.harmonicMidA_le_next
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.harmonicCutoffCross_le_adjShell_mul_D
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.harmonicMassCross_mul_midD_eq
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.harmonicPureCutoffCross_nonneg
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.harmonicMidD_eq_driftSum
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.harmonicMidA_eq_driftSum
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.harmonicWeightCross_eq_driftCovariance
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.no_adj_le_sq_drift_order_at_k3
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.no_sq_le_adj_drift_order_at_k3
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.inverse_square_relative_mass_drift_fails_at_zero
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.inverse_square_relative_mass_drift_fails_at_one
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.unit_inverse_square_additive_mass_drift_fails_at_two
#print axioms YMGap.Continuum.HarmonicWeightDriftFence.two_inverse_square_additive_prefix
