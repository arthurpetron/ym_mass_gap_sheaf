/-
Global recurrence carrier for the full moving-determinant residual.

The pointwise `50/9` allocation is false at the first tail scale.  This file
therefore keeps the complete antisymmetric square.  Twice the fixed-cutoff
weight determinant is decomposed exactly into

  pair residual + pair budget + twice the favorable terminal column.

The `pair residual` is the global carrier containing both the positive
diagonal excess and the negative off-diagonal reserve.  After adjoining the
moving cutoff shell, the cutoff-normalized full slack has an exact
`k -> k+1` recurrence with separate payment, off-diagonal-carrier, and regular
demand increments.  No pointwise kernel envelope is used.
-/

import YMGap.Continuum.HarmonicMovingDeterminantDirect
import YMGap.Continuum.HarmonicMovingDeterminantTail
import YMGap.Continuum.BondMovingScaledNorm
import YMGap.Continuum.HarmonicBulkThetaTail
import YMGap.Continuum.FusionUTuranTrunc

namespace YMGap.Continuum.HarmonicMovingDeterminantRecurrence

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BakryEmery
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.AllWindowCorrDirichlet
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.FusionCoreStepRoundH
open YMGap.Continuum.FusionUTuranTrunc
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicBulkThetaTail
open YMGap.Continuum.HarmonicMovingDeterminantDirect
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.HarmonicDABoundTransport
open YMGap.Continuum.QuadraticCutoffSchedule

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

/-! ## 1. Exact global off-diagonal carrier -/

/-- The complete doubled fixed-cutoff weight carrier.  The first summand is
the antisymmetric residual rectangle; it is not split into pointwise cells. -/
def globalWeightCarrier (k : Nat) : Q' :=
  (driftPairResidualSum k + driftPairBudgetSum k) +
    (driftBoundary k + driftBoundary k)

/-- Restoring the moving-cutoff part gives the complete doubled mass-cross
carrier. -/
def globalMassCrossCarrier (k : Nat) : Q' :=
  globalWeightCarrier k +
    (harmonicCutoffCross k + harmonicCutoffCross k)

/-- The unpaid core plus its exact pair budget reconstructs twice the square
core. -/
theorem driftCore_twice_eq_pairResidual_add_budget (k : Nat) :
    driftCore k + driftCore k ≈
      driftPairResidualSum k + driftPairBudgetSum k := by
  have hcancel :
      ((driftCore k + driftCore k - driftPairBudgetSum k) +
        driftPairBudgetSum k) ≈ driftCore k + driftCore k := by
    refine Q'.eqv_trans _
      ((driftCore k + driftCore k) +
        (-driftPairBudgetSum k + driftPairBudgetSum k)) _
      (Q'.add_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ ((driftCore k + driftCore k) + 0) _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.neg_add_self_eqv (driftPairBudgetSum k))) ?_
    exact QPoly.q_add_zero_eqv _
  refine Q'.eqv_trans _
    ((driftCore k + driftCore k - driftPairBudgetSum k) +
      driftPairBudgetSum k) _ (Q'.eqv_symm hcancel) ?_
  exact Q'.add_eqv_congr_right _ _ _
    (core_twice_sub_pairBudget_eq_residual k)

/-- Twice the fixed-cutoff determinant is exactly the global carrier.  In
particular, all negative off-diagonal reserve remains present. -/
theorem harmonicWeightCross_twice_eq_globalCarrier (k : Nat) :
    harmonicWeightCross k + harmonicWeightCross k ≈
      globalWeightCarrier k := by
  have hw := harmonicWeightCross_eq_core_add_boundary k
  refine Q'.eqv_trans _
    ((driftCore k + driftBoundary k) +
      (driftCore k + driftBoundary k)) _
    (Q'.add_eqv_congr' hw hw) ?_
  refine Q'.eqv_trans _
    ((driftCore k + driftCore k) +
      (driftBoundary k + driftBoundary k)) _ (by ring_qeqv) ?_
  unfold globalWeightCarrier
  exact Q'.add_eqv_congr_right _ _ _
    (driftCore_twice_eq_pairResidual_add_budget k)

/-- Twice the full moving determinant, including the cutoff shell, is the
global mass-cross carrier. -/
theorem harmonicMassCross_twice_eq_globalCarrier (k : Nat) :
    harmonicMassCross k + harmonicMassCross k ≈
      globalMassCrossCarrier k := by
  have hx := harmonicMassCross_eq_weight_add_cutoff k
  refine Q'.eqv_trans _
    ((harmonicWeightCross k + harmonicCutoffCross k) +
      (harmonicWeightCross k + harmonicCutoffCross k)) _
    (Q'.add_eqv_congr' hx hx) ?_
  refine Q'.eqv_trans _
    ((harmonicWeightCross k + harmonicWeightCross k) +
      (harmonicCutoffCross k + harmonicCutoffCross k)) _
    (by ring_qeqv) ?_
  unfold globalMassCrossCarrier
  exact Q'.add_eqv_congr_right _ _ _
    (harmonicWeightCross_twice_eq_globalCarrier k)

/-! ## 2. Cutoff-normalized coupled slack -/

/-- The quadratic cutoff scale used to normalize the inverse-square slack. -/
def movingCutoffScale (k : Nat) : Q' := Q'.ofNat (Ncut k)

theorem movingCutoffScale_pos (k : Nat) :
    (0 : Q') < movingCutoffScale k := by
  unfold movingCutoffScale Ncut
  exact Q'.ofNat_succ_pos ((k + 2) * (k + 2) - 1)

/-- Twice the full residual, multiplied by the quadratic cutoff.  This is the
division-free normalized slack used by the recurrence. -/
def normalizedGlobalSlack (k : Nat) : Q' :=
  movingCutoffScale k *
    (movingDetSpacingResidual k + movingDetSpacingResidual k)

def normalizedPayment (k : Nat) : Q' :=
  movingCutoffScale k *
    (movingSpacingPayment k + movingSpacingPayment k)

/-- The signed global pair residual.  Negative off-diagonal mass appears here
with its original sign and is carried from one scale to the next. -/
def normalizedOffDiagonalCarrier (k : Nat) : Q' :=
  (movingCutoffScale k * shellDropFraction * harmonicSpacing k) *
    driftPairResidualSum k

/-- The remainder of the exact doubled demand: canonical pair budget,
terminal column, and moving cutoff shell. -/
def regularDemandCarrier (k : Nat) : Q' :=
  driftPairBudgetSum k +
    (driftBoundary k + driftBoundary k) +
    (harmonicCutoffCross k + harmonicCutoffCross k)

def normalizedRegularDemand (k : Nat) : Q' :=
  (movingCutoffScale k * shellDropFraction * harmonicSpacing k) *
    regularDemandCarrier k

private theorem double_scaled_sub_algebra
    (p r x s carrier : Q') (hx : x + x ≈ carrier) :
    (p - (r * x) * s) + (p - (r * x) * s) ≈
      (p + p) - (r * carrier) * s := by
  refine Q'.eqv_trans _
    ((p + p) + -((r * (x + x)) * s)) _ ?_ ?_
  · change (p + -((r * x) * s)) + (p + -((r * x) * s)) ≈
      (p + p) + -((r * (x + x)) * s)
    ring_qeqv
  exact Q'.add_eqv_congr_left (p + p) _ _
    (Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_right _ _ s
        (Q'.mul_eqv_congr_left r _ _ hx)))

/-- Exact doubled full-residual formula in terms of the global mass-cross
carrier. -/
theorem movingDetSpacingResidual_twice_eq_globalCarrier (k : Nat) :
    movingDetSpacingResidual k + movingDetSpacingResidual k ≈
      (movingSpacingPayment k + movingSpacingPayment k) -
        (shellDropFraction * globalMassCrossCarrier k) * harmonicSpacing k := by
  unfold movingDetSpacingResidual movingSpacingPayment
  exact double_scaled_sub_algebra
    (((harmonicD k - harmonicA k) *
      (harmonicSpacing k - harmonicSpacing (k + 1))) * harmonicD (k + 1))
    shellDropFraction (harmonicMassCross k) (harmonicSpacing k)
    (globalMassCrossCarrier k)
    (harmonicMassCross_twice_eq_globalCarrier k)

/-- The global mass-cross carrier is the signed pair residual plus the
regular demand carrier. -/
theorem globalMassCrossCarrier_eq_offDiagonal_add_regular (k : Nat) :
    globalMassCrossCarrier k ≈
      driftPairResidualSum k + regularDemandCarrier k := by
  unfold globalMassCrossCarrier globalWeightCarrier regularDemandCarrier
  ring_qeqv

private theorem normalized_decomposition_algebra
    (scale p r x y s raw : Q')
    (hraw : raw + raw ≈ (p + p) - (r * (x + y)) * s) :
    scale * (raw + raw) ≈
      scale * (p + p) - (scale * r * s) * x - (scale * r * s) * y := by
  refine Q'.eqv_trans _
    (scale * ((p + p) - (r * (x + y)) * s)) _
    (Q'.mul_eqv_congr_left scale _ _ hraw) ?_
  change scale * ((p + p) + -((r * (x + y)) * s)) ≈
    scale * (p + p) + -((scale * r * s) * x) +
      -((scale * r * s) * y)
  ring_qeqv

/-- **Normalized global decomposition.**  The cutoff-normalized slack is
payment minus the signed off-diagonal carrier minus the regular demand. -/
theorem normalizedGlobalSlack_eq_payment_sub_offDiagonal_sub_regular (k : Nat) :
    normalizedGlobalSlack k ≈
      normalizedPayment k - normalizedOffDiagonalCarrier k -
        normalizedRegularDemand k := by
  unfold normalizedGlobalSlack normalizedPayment normalizedOffDiagonalCarrier
    normalizedRegularDemand
  apply normalized_decomposition_algebra
  refine Q'.eqv_trans _
    ((movingSpacingPayment k + movingSpacingPayment k) -
      (shellDropFraction * globalMassCrossCarrier k) * harmonicSpacing k) _
    (movingDetSpacingResidual_twice_eq_globalCarrier k) ?_
  exact Q'.add_eqv_congr_left
    (movingSpacingPayment k + movingSpacingPayment k) _ _
    (Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_right _ _ (harmonicSpacing k)
        (Q'.mul_eqv_congr_left shellDropFraction _ _
          (globalMassCrossCarrier_eq_offDiagonal_add_regular k))))

/-! ## 3. Exact balanced `k -> k+1` recurrence -/

/-- Total normalized demand.  The off-diagonal carrier remains a distinct
summand in the definition, so it cannot be silently discarded. -/
def normalizedTotalDemand (k : Nat) : Q' :=
  normalizedOffDiagonalCarrier k + normalizedRegularDemand k

private theorem decomposition_balance_algebra
    (S P O R : Q') (h : S ≈ P - O - R) :
    S + (O + R) ≈ P := by
  refine Q'.eqv_trans _ ((P - O - R) + (O + R)) _
    (Q'.add_eqv_congr_right _ _ (O + R) h) ?_
  change (((P + -O) + -R) + (O + R)) ≈ P
  refine Q'.eqv_trans _
    (P + ((-O + O) + (-R + R))) _ (by ring_qeqv) ?_
  have hO : -O + O ≈ (0 : Q') := by
    exact Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (-O) O)
      (Q'.add_neg_self_eqv O)
  have hR : -R + R ≈ (0 : Q') := by
    exact Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (-R) R)
      (Q'.add_neg_self_eqv R)
  refine Q'.eqv_trans _ (P + ((0 : Q') + 0)) _
    (Q'.add_eqv_congr_left P _ _ (Q'.add_eqv_congr' hO hR)) ?_
  refine Q'.eqv_trans _ (P + 0) _
    (Q'.add_eqv_congr_left P _ _ (QPoly.q_zero_add_eqv 0)) ?_
  exact QPoly.q_add_zero_eqv P

/-- At each scale, normalized slack plus total global demand equals payment. -/
theorem normalizedGlobalSlack_balance (k : Nat) :
    normalizedGlobalSlack k + normalizedTotalDemand k ≈
      normalizedPayment k := by
  unfold normalizedTotalDemand
  exact decomposition_balance_algebra _ _ _ _
    (normalizedGlobalSlack_eq_payment_sub_offDiagonal_sub_regular k)

/-- **Exact balanced global transition.**  This is the cancellation-free
recurrence.  The next signed residual rectangle is transported wholesale in
`normalizedTotalDemand (k+1)`. -/
theorem normalizedGlobalSlack_balanced_succ (k : Nat) :
    (normalizedGlobalSlack (k + 1) + normalizedTotalDemand (k + 1)) +
        normalizedPayment k ≈
      (normalizedGlobalSlack k + normalizedTotalDemand k) +
        normalizedPayment (k + 1) := by
  refine Q'.eqv_trans _
    (normalizedPayment (k + 1) + normalizedPayment k) _
    (Q'.add_eqv_congr_right _ _ _
      (normalizedGlobalSlack_balance (k + 1))) ?_
  refine Q'.eqv_trans _
    (normalizedPayment k + normalizedPayment (k + 1)) _
    (Q'.add_comm_eqv _ _) ?_
  exact Q'.add_eqv_congr_right _ _ (normalizedPayment (k + 1))
    (Q'.eqv_symm (normalizedGlobalSlack_balance k))

private theorem le_of_add_le_add_right_local {a b c : Q'}
    (h : a + c ≤ b + c) : a ≤ b := by
  have hadd := Q'.add_le_add_right (a + c) (b + c) (-c) h
  have hleft : (a + c) + -c ≈ a := by
    refine Q'.eqv_trans _ (a + (c + -c)) _
      (Q'.add_assoc_eqv a c (-c)) ?_
    refine Q'.eqv_trans _ (a + 0) _
      (Q'.add_eqv_congr_left a _ _ (Q'.add_neg_self_eqv c)) ?_
    exact QPoly.q_add_zero_eqv a
  have hright : (b + c) + -c ≈ b := by
    refine Q'.eqv_trans _ (b + (c + -c)) _
      (Q'.add_assoc_eqv b c (-c)) ?_
    refine Q'.eqv_trans _ (b + 0) _
      (Q'.add_eqv_congr_left b _ _ (Q'.add_neg_self_eqv c)) ?_
    exact QPoly.q_add_zero_eqv b
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright))

private theorem le_of_add_le_add_left_local {a b c : Q'}
    (h : c + a ≤ c + b) : a ≤ b := by
  apply le_of_add_le_add_right_local (c := c)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_comm_eqv a c))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.add_comm_eqv c b)))

private theorem normalizedGlobalSlack_transition_assoc (k : Nat) :
    normalizedGlobalSlack (k + 1) +
        (normalizedTotalDemand (k + 1) + normalizedPayment k) ≈
      normalizedGlobalSlack k +
        (normalizedTotalDemand k + normalizedPayment (k + 1)) := by
  refine Q'.eqv_trans _
    ((normalizedGlobalSlack (k + 1) + normalizedTotalDemand (k + 1)) +
      normalizedPayment k) _
    (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _
    ((normalizedGlobalSlack k + normalizedTotalDemand k) +
      normalizedPayment (k + 1)) _
    (normalizedGlobalSlack_balanced_succ k) ?_
  exact Q'.add_assoc_eqv _ _ _

/-- The balance premise is exactly monotonicity of the normalized full slack.
This fences the balanced identity from being mistaken for an independent
contraction estimate. -/
theorem normalizedBalance_iff_slack_mono (k : Nat) :
    (normalizedTotalDemand (k + 1) + normalizedPayment k ≤
      normalizedTotalDemand k + normalizedPayment (k + 1)) ↔
    (normalizedGlobalSlack k ≤ normalizedGlobalSlack (k + 1)) := by
  let C := normalizedTotalDemand (k + 1) + normalizedPayment k
  let B := normalizedTotalDemand k + normalizedPayment (k + 1)
  have hrec : normalizedGlobalSlack (k + 1) + C ≈
      normalizedGlobalSlack k + B := by
    dsimp only [C, B]
    exact normalizedGlobalSlack_transition_assoc k
  constructor
  · intro hbalance
    have hadd : normalizedGlobalSlack k + C ≤
        normalizedGlobalSlack k + B := by
      apply Q'.add_le_add_left
      dsimp only [C, B]
      exact hbalance
    have htransport : normalizedGlobalSlack k + C ≤
        normalizedGlobalSlack (k + 1) + C :=
      Q'.le_trans' _ _ _ hadd (Q'.ge_of_eqv hrec)
    exact le_of_add_le_add_right_local htransport
  · intro hmono
    have hadd : normalizedGlobalSlack k + C ≤
        normalizedGlobalSlack (k + 1) + C :=
      Q'.add_le_add_right _ _ C hmono
    have htransport : normalizedGlobalSlack k + C ≤
        normalizedGlobalSlack k + B :=
      Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hrec)
    have hCB : C ≤ B := le_of_add_le_add_left_local htransport
    dsimp only [C, B] at hCB
    exact hCB

/-! ## 4. Exact boundary adjudication -/

/-- Split the full normalizer at mode `20`.  The remaining finite window is
the same degree-two Casimir tail controlled by `tail_modulus`. -/
private theorem harmonicD_eq_prefix19_add_tail20 (k : Nat)
    (hk : 20 ≤ Ncut k + 1) :
    harmonicD k ≈ coordNormSq (harmW k) 19 +
      tailWindow (harmW k * harmW k) 2 20 (Ncut k + 1 - 20) := by
  let f : Nat → Q' := fun a => coeffW (harmW k) a * coeffW (harmW k) a
  let M := Ncut k + 1 - 20
  have hsplit : fsum f (Ncut k + 1) ≈
      fsum f 20 + fsum (fun r => f (20 + r)) M := by
    have h := fsum_split_at f 20 M
    dsimp only [M] at h ⊢
    rw [Nat.add_sub_of_le hk] at h
    exact h
  have htail : fsum (fun r => f (20 + r)) M ≈
      tailWindow (harmW k * harmW k) 2 20 M := by
    unfold tailWindow
    rw [MovingCutoff.fsum_eq_finSum]
    exact RationalTail.finSum_eqv_congr _ _
      (fun r => by
        dsimp only [f]
        exact coeffSqTerm_eqv_tailTerm k (20 + r)) M
  unfold harmonicD coordNormSq
  dsimp only [f] at hsplit
  refine Q'.eqv_trans _ _ _ hsplit ?_
  exact Q'.add_eqv_congr_left _ _ _ htail

private theorem harmonicSquaredTail20_le_dyad20 (k : Nat)
    (hk : k = 37 ∨ k = 38 ∨ k = 39) :
    ∀ M, tailWindow (harmW k * harmW k) 2 20 M ≤ dyad 20 := by
  rcases hk with rfl | rfl | rfl
  all_goals
    apply tail_modulus
    all_goals decide

private theorem tailWindow_nonneg_local {w : Q'} (hw : (0 : Q') ≤ w)
    (m S M : Nat) : (0 : Q') ≤ tailWindow w m S M := by
  unfold tailWindow
  rw [← MovingCutoff.fsum_eq_finSum]
  exact fsum_nonneg
    (fun j => tailTerm_nonneg hw m (S + j)) M

private theorem harmonicD_prefix19_le (k : Nat) (hk : 20 ≤ Ncut k + 1) :
    coordNormSq (harmW k) 19 ≤ harmonicD k := by
  let T := tailWindow (harmW k * harmW k) 2 20 (Ncut k + 1 - 20)
  have hT0 : (0 : Q') ≤ T := by
    dsimp only [T]
    exact tailWindow_nonneg_local
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _ _ _
  have hadd : coordNormSq (harmW k) 19 ≤ coordNormSq (harmW k) 19 + T :=
    Q'.add_le_self_of_nonneg _ _ hT0
  exact Q'.le_trans' _ _ _ hadd
    (Q'.ge_of_eqv (by
      dsimp only [T]
      exact harmonicD_eq_prefix19_add_tail20 k hk))

private theorem harmonicD_le_prefix19_add_dyad20 (k : Nat)
    (hk : k = 37 ∨ k = 38 ∨ k = 39) :
    harmonicD k ≤ coordNormSq (harmW k) 19 + dyad 20 := by
  have hk20 : 20 ≤ Ncut k + 1 := by
    rcases hk with rfl | rfl | rfl <;> decide
  let T := tailWindow (harmW k * harmW k) 2 20 (Ncut k + 1 - 20)
  have hT : T ≤ dyad 20 := by
    dsimp only [T]
    exact harmonicSquaredTail20_le_dyad20 k hk _
  have hadd : coordNormSq (harmW k) 19 + T ≤
      coordNormSq (harmW k) 19 + dyad 20 :=
    Q'.add_le_add_left _ _ _ hT
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by
      dsimp only [T]
      exact harmonicD_eq_prefix19_add_tail20 k hk20)) hadd

theorem harmonicD_lower_k37 :
    Q'.mkPos 394172 10000 (by decide) ≤ harmonicD 37 := by
  exact Q'.le_trans' _ _ _ (by decide)
    (harmonicD_prefix19_le 37 (by decide))

theorem harmonicD_upper_k37 :
    harmonicD 37 ≤ Q'.mkPos 394173 10000 (by decide) := by
  exact Q'.le_trans' _ _ _
    (harmonicD_le_prefix19_add_dyad20 37 (Or.inl rfl)) (by decide)

theorem harmonicD_lower_k38 :
    Q'.mkPos 409092 10000 (by decide) ≤ harmonicD 38 := by
  exact Q'.le_trans' _ _ _ (by decide)
    (harmonicD_prefix19_le 38 (by decide))

theorem harmonicD_upper_k38 :
    harmonicD 38 ≤ Q'.mkPos 409093 10000 (by decide) := by
  exact Q'.le_trans' _ _ _
    (harmonicD_le_prefix19_add_dyad20 38 (Or.inr (Or.inl rfl))) (by decide)

theorem harmonicD_lower_k39 :
    Q'.mkPos 424195 10000 (by decide) ≤ harmonicD 39 := by
  exact Q'.le_trans' _ _ _ (by decide)
    (harmonicD_prefix19_le 39 (by decide))

theorem harmonicD_upper_k39 :
    harmonicD 39 ≤ Q'.mkPos 424198 10000 (by decide) := by
  exact Q'.le_trans' _ _ _
    (harmonicD_le_prefix19_add_dyad20 39 (Or.inr (Or.inr rfl))) (by decide)

theorem harmonicMass_upper20_k37 :
    harmonicMass 37 ≤ Q'.mkPos 38545 1000000 (by decide) := by
  exact harmonicMass_le_of_prefix 37 19 1502 _ (by decide) (by decide)

theorem harmonicMass_upper20_k38 :
    harmonicMass 38 ≤ Q'.mkPos 37579 1000000 (by decide) := by
  exact harmonicMass_le_of_prefix 38 19 1581 _ (by decide) (by decide)

theorem harmonicMass_upper20_k39 :
    harmonicMass 39 ≤ Q'.mkPos 36661 1000000 (by decide) := by
  exact harmonicMass_le_of_prefix 39 19 1662 _ (by decide) (by decide)

private theorem dirichletEnergy_mono_from20 (k : Nat)
    (hk : 20 ≤ Ncut k) :
    dirichletEnergy (harmW k) 20 ≤
      dirichletEnergy (harmW k) (Ncut k) := by
  unfold dirichletEnergy
  apply fsum_le_extend
  · intro i
    exact Q'.le_trans' _ _ _
      (SumOfSquares.q_mul_self_nonneg
        (coeffW (harmW k) i + (-coeffW (harmW k) (i + 1))))
      (Q'.le_of_eqv (Q'.eqv_symm
        (dirichletTerm_eqv_sq
          (coeffW (harmW k) i) (coeffW (harmW k) (i + 1)))))
  · exact hk

private theorem prefixDirichlet_le_twice_deficit (k : Nat)
    (hk : 20 ≤ Ncut k) :
    (1 : Q') + dirichletEnergy (harmW k) 20 ≤
      Q'.ofNat 2 * (harmonicD k - harmonicA k) := by
  let c0 := coeffW (harmW k) 0
  let cN := coeffW (harmW k) (Ncut k)
  let E20 := dirichletEnergy (harmW k) 20
  let EN := dirichletEnergy (harmW k) (Ncut k)
  have hc0 : c0 * c0 ≈ (1 : Q') := by
    dsimp only [c0]
    rw [coeffW_zero]
    exact Q'.one_mul_eqv 1
  have hcN0 : (0 : Q') ≤ cN * cN := SumOfSquares.q_mul_self_nonneg cN
  have hE : E20 ≤ EN := by
    dsimp only [E20, EN]
    exact dirichletEnergy_mono_from20 k hk
  have hhead : (1 : Q') + E20 ≤ c0 * c0 + EN := by
    exact Q'.add_le_add (Q'.le_of_eqv (Q'.eqv_symm hc0)) hE
  have hboundary : c0 * c0 + EN ≤ (c0 * c0 + cN * cN) + EN := by
    have hadd : c0 * c0 ≤ c0 * c0 + cN * cN :=
      Q'.add_le_self_of_nonneg _ _ hcN0
    exact Q'.add_le_add_right _ _ EN hadd
  have hid := twice_norm_sub_corr_eq_boundary_dirichlet
    (harmW k) (Ncut k)
  change (1 : Q') + E20 ≤ Q'.ofNat 2 *
    (coordNormSq (harmW k) (Ncut k) +
      (-adjCorr (harmW k) (Ncut k)))
  exact Q'.le_trans' _ _ _ hhead
    (Q'.le_trans' _ _ _ hboundary (Q'.ge_of_eqv hid))

private theorem deficit_lower_of_prefix20 (k : Nat) (L : Q')
    (hk : 20 ≤ Ncut k)
    (hclosed : L * Q'.ofNat 2 ≤
      (1 : Q') + dirichletEnergy (harmW k) 20) :
    L ≤ harmonicD k - harmonicA k := by
  have hscaled : L * Q'.ofNat 2 ≤
      Q'.ofNat 2 * (harmonicD k - harmonicA k) :=
    Q'.le_trans' _ _ _ hclosed (prefixDirichlet_le_twice_deficit k hk)
  have hscaled' : L * Q'.ofNat 2 ≤
      (harmonicD k - harmonicA k) * Q'.ofNat 2 :=
    Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
  exact le_of_mul_le_mul_right_pos (by decide) hscaled'

theorem harmonicDeficit_lower_k37 :
    Q'.mkPos 151929 100000 (by decide) ≤ harmonicD 37 - harmonicA 37 := by
  exact deficit_lower_of_prefix20 37 _ (by decide) (by decide)

theorem harmonicDeficit_lower_k38 :
    Q'.mkPos 153729 100000 (by decide) ≤ harmonicD 38 - harmonicA 38 := by
  exact deficit_lower_of_prefix20 38 _ (by decide) (by decide)

theorem harmonicDeficit_lower_k39 :
    Q'.mkPos 155508 100000 (by decide) ≤ harmonicD 39 - harmonicA 39 := by
  exact deficit_lower_of_prefix20 39 _ (by decide) (by decide)

private theorem deficit_upper_of_mass_D
    (k : Nat) (U DU : Q')
    (hm : harmonicMass k ≤ U) (hD : harmonicD k ≤ DU)
    (hU0 : (0 : Q') ≤ U) :
    harmonicD k - harmonicA k ≤ U * DU := by
  have hprod : harmonicMass k * harmonicD k ≤ U * DU :=
    Q'.mul_le_mul_of_nonneg hm hD hU0 (Q'.le_of_lt (harmonicD_pos k))
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (harmonicMass_mul_D_eqv k)) hprod

theorem harmonicDeficit_upper_k37 :
    harmonicD 37 - harmonicA 37 ≤
      Q'.mkPos 38545 1000000 (by decide) *
        Q'.mkPos 394173 10000 (by decide) := by
  exact deficit_upper_of_mass_D 37 _ _ harmonicMass_upper20_k37
    harmonicD_upper_k37 (by decide)

theorem harmonicDeficit_upper_k38 :
    harmonicD 38 - harmonicA 38 ≤
      Q'.mkPos 37579 1000000 (by decide) *
        Q'.mkPos 409093 10000 (by decide) := by
  exact deficit_upper_of_mass_D 38 _ _ harmonicMass_upper20_k38
    harmonicD_upper_k38 (by decide)

theorem harmonicDeficit_upper_k39 :
    harmonicD 39 - harmonicA 39 ≤
      Q'.mkPos 36661 1000000 (by decide) *
        Q'.mkPos 424198 10000 (by decide) := by
  exact deficit_upper_of_mass_D 39 _ _ harmonicMass_upper20_k39
    harmonicD_upper_k39 (by decide)

private theorem collect_twice_plus_algebra
    (C E d D r X s : Q') :
    C * ((((E * d) * D) + -((r * X) * s)) +
      (((E * d) * D) + -((r * X) * s))) ≈
    (((((C * d) * E) * D)) + -((((C * s) * r) * X))) +
      (((((C * d) * E) * D)) + -((((C * s) * r) * X))) := by
  ring_qeqv

private theorem quotient_cross_cancel_local (D0 A0 D1 A1 : Q') :
    (D0 - A0) * D1 + -((D1 - A1) * D0) ≈
      A1 * D0 + -(A0 * D1) := by
  have hleft : (D0 - A0) * D1 ≈ D0 * D1 + -(A0 * D1) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv D0 (-A0) D1) ?_
    exact Q'.add_eqv_congr_left _ _ _ (Q'.neg_mul_eqv A0 D1)
  have hright : -((D1 - A1) * D0) ≈ -(D1 * D0) + A1 * D0 := by
    refine Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.add_mul_eqv D1 (-A1) D0)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.neg_add_eqv (D1 * D0) ((-A1) * D0)) ?_
    refine Q'.add_eqv_congr_left (-(D1 * D0)) _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.neg_mul_eqv A1 D0)) ?_
    exact Q'.neg_neg_eqv (A1 * D0)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hleft hright) ?_
  refine Q'.eqv_trans _ _ _
    (QPoly.q_interchange (D0 * D1) (-(A0 * D1))
      (-(D1 * D0)) (A1 * D0)) ?_
  have hcancel : D0 * D1 + -(D1 * D0) ≈ (0 : Q') := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (D0 * D1) _ _
        (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv D1 D0))) ?_
    exact Q'.add_neg_self_eqv (D0 * D1)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ hcancel) ?_
  refine Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv _) ?_
  exact Q'.add_comm_eqv (-(A0 * D1)) (A1 * D0)

private theorem signed_three_reorder (a b c : Q') :
    (a + -b) + c ≈ c + (-b + a) := by
  ring_qeqv

private theorem weighted_cross_regroup
    (r g U V X : Q') (hX : X ≈ U - V) :
    g * U - r * X ≈ r * V - ((r - g) * U) := by
  let a := g * U
  let b := r * U
  let c := r * V
  have hmulX : r * X ≈ b + -c := by
    refine Q'.eqv_trans _ (r * (U - V)) _
      (Q'.mul_eqv_congr_left r _ _ hX) ?_
    refine Q'.eqv_trans _ (r * U + r * (-V)) _
      (Q'.mul_add_eqv r U (-V)) ?_
    exact Q'.add_eqv_congr_left (r * U) _ _ (Q'.mul_neg_eqv r V)
  have hnegX : -(r * X) ≈ -b + c := by
    refine Q'.eqv_trans _ (-(b + -c)) _
      (Q'.neg_eqv_congr _ _ hmulX) ?_
    refine Q'.eqv_trans _ (-b + -(-c)) _
      (Q'.neg_add_eqv b (-c)) ?_
    exact Q'.add_eqv_congr_left (-b) _ _ (Q'.neg_neg_eqv c)
  have hleft : g * U - r * X ≈ (a + -b) + c := by
    refine Q'.eqv_trans _ (a + (-b + c)) _
      (Q'.add_eqv_congr_left a _ _ hnegX) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv a (-b) c)
  have hmulRG : (r - g) * U ≈ b + -a := by
    refine Q'.eqv_trans _ (r * U + (-g) * U) _
      (Q'.add_mul_eqv r (-g) U) ?_
    exact Q'.add_eqv_congr_left (r * U) _ _ (Q'.neg_mul_eqv g U)
  have hnegRG : -((r - g) * U) ≈ -b + a := by
    refine Q'.eqv_trans _ (-(b + -a)) _
      (Q'.neg_eqv_congr _ _ hmulRG) ?_
    refine Q'.eqv_trans _ (-b + -(-a)) _
      (Q'.neg_add_eqv b (-a)) ?_
    exact Q'.add_eqv_congr_left (-b) _ _ (Q'.neg_neg_eqv a)
  have hright : r * V - ((r - g) * U) ≈ c + (-b + a) :=
    Q'.add_eqv_congr_left c _ _ hnegRG
  exact Q'.eqv_trans _ ((a + -b) + c) _ hleft
    (Q'.eqv_trans _ (c + (-b + a)) _
      (signed_three_reorder a b c) (Q'.eqv_symm hright))

private theorem cross_regroup_plus_algebra
    (D0 A0 D1 A1 r g : Q') :
    let L := (g * (D0 + -A0)) * D1 +
      -(r * ((A1 * D0) + -(A0 * D1)))
    let R := (r * (D1 + -A1)) * D0 +
      -(((r + -g) * (D0 + -A0)) * D1)
    L + L ≈ R + R := by
  dsimp only
  have hone :
      (g * (D0 + -A0)) * D1 +
          -(r * ((A1 * D0) + -(A0 * D1))) ≈
        (r * (D1 + -A1)) * D0 +
          -(((r + -g) * (D0 + -A0)) * D1) := by
    let U := (D0 + -A0) * D1
    let V := (D1 + -A1) * D0
    let X := (A1 * D0) + -(A0 * D1)
    have hX : X ≈ U - V := by
      dsimp only [U, V, X]
      exact Q'.eqv_symm (quotient_cross_cancel_local D0 A0 D1 A1)
    have hbase := weighted_cross_regroup r g U V X hX
    refine Q'.eqv_trans _ (g * U - r * X) _ ?_ ?_
    · dsimp only [U, X]
      exact Q'.add_eqv_congr_right _ _ _
        (Q'.mul_assoc_eqv g (D0 + -A0) D1)
    refine Q'.eqv_trans _ (r * V - ((r - g) * U)) _ hbase ?_
    dsimp only [U, V]
    exact Q'.add_eqv_congr'
      (Q'.eqv_symm (Q'.mul_assoc_eqv r (D1 + -A1) D0))
      (Q'.neg_eqv_congr _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (r - g) (D0 + -A0) D1)))
  exact Q'.add_eqv_congr' hone hone

private theorem normalized_boundary_algebra
    (C s t D0 A0 D1 A1 r g c : Q')
    (hgap : C * (s - t) ≈ g) (hunit : C * s ≈ (1 : Q'))
    (hc : r - g ≈ c) :
    C *
        ((((D0 - A0) * (s - t)) * D1 -
            (r * (A1 * D0 - A0 * D1)) * s) +
          (((D0 - A0) * (s - t)) * D1 -
            (r * (A1 * D0 - A0 * D1)) * s)) ≈
      (((r * (D1 - A1)) * D0 - (c * (D0 - A0)) * D1) +
        ((r * (D1 - A1)) * D0 - (c * (D0 - A0)) * D1)) := by
  let E0 := D0 - A0
  let E1 := D1 - A1
  let X := A1 * D0 - A0 * D1
  have hcollect :
      C * (((E0 * (s - t)) * D1 - (r * X) * s) +
        ((E0 * (s - t)) * D1 - (r * X) * s)) ≈
      (((((C * (s - t)) * E0) * D1) - (((C * s) * r) * X)) +
        ((((C * (s - t)) * E0) * D1) - (((C * s) * r) * X))) := by
    dsimp only [E0, X]
    exact collect_twice_plus_algebra C (D0 - A0) (s - t) D1 r
      (A1 * D0 - A0 * D1) s
  have hleft : ((C * (s - t)) * E0) * D1 ≈ (g * E0) * D1 :=
    Q'.mul_eqv_congr_right _ _ D1
      (Q'.mul_eqv_congr_right _ _ E0 hgap)
  have hright : ((C * s) * r) * X ≈ r * X := by
    refine Q'.mul_eqv_congr_right _ _ X ?_
    exact Q'.eqv_trans _ ((1 : Q') * r) _
      (Q'.mul_eqv_congr_right _ _ r hunit) (Q'.one_mul_eqv r)
  have hreplace :
      (((((C * (s - t)) * E0) * D1) - (((C * s) * r) * X)) +
        ((((C * (s - t)) * E0) * D1) - (((C * s) * r) * X))) ≈
      ((((g * E0) * D1) - (r * X)) +
        (((g * E0) * D1) - (r * X))) := by
    have hone :
        ((((C * (s - t)) * E0) * D1) - (((C * s) * r) * X)) ≈
        (((g * E0) * D1) - (r * X)) :=
      Q'.add_eqv_congr' hleft (Q'.neg_eqv_congr _ _ hright)
    exact Q'.add_eqv_congr' hone hone
  have hregroup :
      ((((g * E0) * D1) - (r * X)) +
        (((g * E0) * D1) - (r * X))) ≈
      ((((r * E1) * D0) - (((r - g) * E0) * D1)) +
        (((r * E1) * D0) - (((r - g) * E0) * D1))) := by
    dsimp only [E0, E1, X]
    exact cross_regroup_plus_algebra D0 A0 D1 A1 r g
  have hcTerm : (((r - g) * E0) * D1) ≈ (c * E0) * D1 :=
    Q'.mul_eqv_congr_right _ _ D1
      (Q'.mul_eqv_congr_right _ _ E0 hc)
  refine Q'.eqv_trans _ _ _ hcollect ?_
  refine Q'.eqv_trans _ _ _ hreplace ?_
  refine Q'.eqv_trans _ _ _ hregroup ?_
  have hone :
      ((r * E1) * D0 - (((r - g) * E0) * D1)) ≈
      ((r * E1) * D0 - ((c * E0) * D1)) :=
    Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hcTerm)
  exact Q'.add_eqv_congr' hone hone

/-- Exact normalized slack at the last banked scale, in positive-product
minus positive-product form. -/
def boundarySlackForm37 : Q' :=
  let core :=
    (shellDropFraction * (harmonicD 38 - harmonicA 38)) * harmonicD 37 -
      (Q'.mkPos 497 1600 (by decide) *
        (harmonicD 37 - harmonicA 37)) * harmonicD 38
  core + core

/-- Exact normalized slack at the first tail scale. -/
def boundarySlackForm38 : Q' :=
  let core :=
    (shellDropFraction * (harmonicD 39 - harmonicA 39)) * harmonicD 38 -
      (Q'.mkPos 13104 42025 (by decide) *
        (harmonicD 38 - harmonicA 38)) * harmonicD 39
  core + core

theorem normalizedGlobalSlack_37_eq_boundaryForm :
    normalizedGlobalSlack 37 ≈ boundarySlackForm37 := by
  unfold normalizedGlobalSlack movingDetSpacingResidual boundarySlackForm37
    harmonicMassCross
  apply normalized_boundary_algebra
    (g := Q'.mkPos 79 1600 (by decide))
    (c := Q'.mkPos 497 1600 (by decide))
  · unfold movingCutoffScale harmonicSpacing Ncut SummableInverseSquare.unit
    decide
  · unfold movingCutoffScale harmonicSpacing Ncut SummableInverseSquare.unit
    decide
  · unfold shellDropFraction
    decide

theorem normalizedGlobalSlack_38_eq_boundaryForm :
    normalizedGlobalSlack 38 ≈ boundarySlackForm38 := by
  unfold normalizedGlobalSlack movingDetSpacingResidual boundarySlackForm38
    harmonicMassCross
  apply normalized_boundary_algebra
    (g := Q'.mkPos 81 1681 (by decide))
    (c := Q'.mkPos 13104 42025 (by decide))
  · unfold movingCutoffScale harmonicSpacing Ncut SummableInverseSquare.unit
    decide
  · unfold movingCutoffScale harmonicSpacing Ncut SummableInverseSquare.unit
    decide
  · unfold shellDropFraction
    decide

/-- Preservation consumer for the balanced recurrence.  It compares total
global demand plus old payment across one scale; no cellwise sign occurs. -/
theorem normalizedGlobalSlack_nonneg_succ_of_balance
    (k : Nat) (h0 : (0 : Q') ≤ normalizedGlobalSlack k)
    (hbalance : normalizedTotalDemand (k + 1) + normalizedPayment k ≤
      normalizedTotalDemand k + normalizedPayment (k + 1)) :
    (0 : Q') ≤ normalizedGlobalSlack (k + 1) := by
  let D1 := normalizedTotalDemand (k + 1) + normalizedPayment k
  let D0 := normalizedTotalDemand k + normalizedPayment (k + 1)
  have hbase : D1 ≤ normalizedGlobalSlack k + D0 := by
    have hD : D1 ≤ D0 := by dsimp only [D1, D0]; exact hbalance
    have hD0 : D0 ≤ normalizedGlobalSlack k + D0 := by
      have hadd := Q'.add_le_add_right (0 : Q') (normalizedGlobalSlack k) D0 h0
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_zero_add_eqv D0)) hadd
    exact Q'.le_trans' _ _ _ hD hD0
  have hrec : normalizedGlobalSlack (k + 1) + D1 ≈
      normalizedGlobalSlack k + D0 := by
    dsimp only [D1, D0]
    refine Q'.eqv_trans _
      ((normalizedGlobalSlack (k + 1) + normalizedTotalDemand (k + 1)) +
        normalizedPayment k) _
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _
      ((normalizedGlobalSlack k + normalizedTotalDemand k) +
        normalizedPayment (k + 1)) _
      (normalizedGlobalSlack_balanced_succ k) ?_
    exact Q'.add_assoc_eqv _ _ _
  have hwith : (0 : Q') + D1 ≤ normalizedGlobalSlack (k + 1) + D1 := by
    exact Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (QPoly.q_zero_add_eqv D1)) hbase)
      (Q'.ge_of_eqv hrec)
  exact le_of_add_le_add_right_local hwith

/-! ## 4. Connection back to the full determinant -/

/-- Nonnegativity of the normalized doubled slack implies the original full
moving-determinant inequality. -/
theorem fullDeterminant_of_normalizedGlobalSlack_nonneg
    (k : Nat) (h : (0 : Q') ≤ normalizedGlobalSlack k) :
    (shellDropFraction * harmonicMassCross k) * harmonicSpacing k ≤
      movingSpacingPayment k := by
  let R := movingDetSpacingResidual k
  let C := movingCutoffScale k
  have hC : (0 : Q') < C := by
    dsimp only [C]
    exact movingCutoffScale_pos k
  have hscaled : (0 : Q') ≤ (R + R) * C := by
    have heq : normalizedGlobalSlack k ≈ (R + R) * C := by
      unfold normalizedGlobalSlack
      dsimp only [R, C]
      exact Q'.mul_comm_eqv _ _
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv heq)
  have hmulC : (0 : Q') * C ≤ (R + R) * C :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.zero_mul_eqv C)) hscaled
  have hdouble0 : (0 : Q') ≤ R + R :=
    le_of_mul_le_mul_right_pos hC hmulC
  have htwo : (0 : Q') ≤ R * Q'.ofNat 2 := by
    exact Q'.le_trans' _ _ _ hdouble0 (Q'.le_of_eqv (by
      exact Q'.eqv_trans _ _ _
        (Q'.eqv_symm (CubeRatioBounds.ofNat_two_mul_eqv R))
        (Q'.mul_comm_eqv (Q'.ofNat 2) R)))
  have hmulTwo : (0 : Q') * Q'.ofNat 2 ≤ R * Q'.ofNat 2 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.zero_mul_eqv _)) htwo
  have hR0 : (0 : Q') ≤ R :=
    le_of_mul_le_mul_right_pos (by decide) hmulTwo
  dsimp only [R, movingDetSpacingResidual] at hR0
  exact Q'.le_of_sub_nonneg hR0

/-- The already banked final prefix supplies a genuine normalized anchor at
`k=37`; the recurrence transition at `k=37` is exactly what would establish
the first unbanked scale `k=38`. -/
theorem normalizedGlobalSlack_nonneg_k37 :
    (0 : Q') ≤ normalizedGlobalSlack 37 := by
  have hdet := fullDeterminant_initial_thirtyEight (k := 37) (by decide)
  have hR0 : (0 : Q') ≤ movingDetSpacingResidual 37 := by
    unfold movingDetSpacingResidual
    exact Q'.sub_nonneg_of_le hdet
  unfold normalizedGlobalSlack
  exact Q'.mul_nonneg _ _
    (Q'.le_of_lt (movingCutoffScale_pos 37))
    (Q'.zero_le_add _ _ hR0 hR0)

/-- Exact one-step consumer for crossing the current prefix/tail boundary. -/
theorem normalizedGlobalSlack_nonneg_k38_of_balance
    (hbalance : normalizedTotalDemand 38 + normalizedPayment 37 ≤
      normalizedTotalDemand 37 + normalizedPayment 38) :
    (0 : Q') ≤ normalizedGlobalSlack 38 := by
  exact normalizedGlobalSlack_nonneg_succ_of_balance
    37 normalizedGlobalSlack_nonneg_k37 hbalance

#print axioms globalWeightCarrier
#print axioms globalMassCrossCarrier
#print axioms driftCore_twice_eq_pairResidual_add_budget
#print axioms harmonicWeightCross_twice_eq_globalCarrier
#print axioms harmonicMassCross_twice_eq_globalCarrier
#print axioms movingCutoffScale
#print axioms movingCutoffScale_pos
#print axioms normalizedGlobalSlack
#print axioms normalizedPayment
#print axioms normalizedOffDiagonalCarrier
#print axioms regularDemandCarrier
#print axioms normalizedRegularDemand
#print axioms movingDetSpacingResidual_twice_eq_globalCarrier
#print axioms globalMassCrossCarrier_eq_offDiagonal_add_regular
#print axioms normalizedGlobalSlack_eq_payment_sub_offDiagonal_sub_regular
#print axioms normalizedTotalDemand
#print axioms normalizedGlobalSlack_balance
#print axioms normalizedGlobalSlack_balanced_succ
#print axioms normalizedBalance_iff_slack_mono
#print axioms harmonicD_lower_k37
#print axioms harmonicD_upper_k37
#print axioms harmonicD_lower_k38
#print axioms harmonicD_upper_k38
#print axioms harmonicD_lower_k39
#print axioms harmonicD_upper_k39
#print axioms harmonicMass_upper20_k37
#print axioms harmonicMass_upper20_k38
#print axioms harmonicMass_upper20_k39
#print axioms harmonicDeficit_lower_k37
#print axioms harmonicDeficit_upper_k37
#print axioms harmonicDeficit_lower_k38
#print axioms harmonicDeficit_upper_k38
#print axioms harmonicDeficit_lower_k39
#print axioms harmonicDeficit_upper_k39
#print axioms boundarySlackForm37
#print axioms boundarySlackForm38
#print axioms normalizedGlobalSlack_37_eq_boundaryForm
#print axioms normalizedGlobalSlack_38_eq_boundaryForm
#print axioms normalizedGlobalSlack_nonneg_succ_of_balance
#print axioms fullDeterminant_of_normalizedGlobalSlack_nonneg
#print axioms normalizedGlobalSlack_nonneg_k37
#print axioms normalizedGlobalSlack_nonneg_k38_of_balance

end YMGap.Continuum.HarmonicMovingDeterminantRecurrence
