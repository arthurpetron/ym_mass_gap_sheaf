/-
Exact Taylor/flux coordinates for the remaining lower-six payment.

The quadratic suffix cannot simply be extrapolated through the adverse
prefix: on a negative next-scale carrier the exact-minus-Taylor drift has
the wrong sign.  This file retains that correction exactly.  It rewrites
the target as

  Taylor prefix + Taylor suffix + exact prefix correction,

with the augmented first Abel cell treated uniformly.  The final section
banks the division-free Hermite flux identities governing the first three
orders of the Taylor block.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticRecovery

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticRecovery
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftScaleStep
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossWindow
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledWindowDifference
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem taylor_flux_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "taylor_flux_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               taylor_flux_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- The retained second-order factor at an ordinary mode. -/
def lowerSixQuadraticTaylorFactor (k n : Nat) : Q' :=
  lowerSixWeightDriftFloor k n + lowerSixWeightDriftQuadratic k n

/-- Ordinary-mode Taylor carrier used on the physical suffix. -/
def lowerSixQuadraticTaylorCarrier (k n : Nat) : Q' :=
  Q'.ofNat (k + 3) * lowerSixQuadraticTaylorFactor k n *
      lowerSixModeCarrier (k + 1) n +
    -(Q'.ofNat (k + 2) * lowerSixModeCarrier k n)

/-- The old-scale weight times the ordinary-mode Taylor carrier. -/
def lowerSixQuadraticTaylorWeightedTerm (k n : Nat) : Q' :=
  lowerSixModeWeight k n * lowerSixQuadraticTaylorCarrier k n

theorem linear_add_quadratic_eqv_taylorCarrier (k n : Nat) :
    lowerSixScaledLinearDriftCarrier k n +
        lowerSixScaledDriftQuadratic k n ≈
      lowerSixQuadraticTaylorCarrier k n := by
  unfold lowerSixScaledLinearDriftCarrier lowerSixScaledDriftQuadratic
    lowerSixQuadraticTaylorCarrier lowerSixQuadraticTaylorFactor
  taylor_flux_ring

/-- Taylor carrier in Abel indexing.  At index zero this automatically
retains the augmented `+4` endpoint carrier. -/
def lowerSixQuadraticTaylorAbelCarrier (k j : Nat) : Q' :=
  Q'.ofNat (k + 3) * lowerSixQuadraticTaylorFactor k (j + 1) *
      lowerSixAbelCarrier (k + 1) j +
    -(Q'.ofNat (k + 2) * lowerSixAbelCarrier k j)

/-- The signed correction which must not be discarded on the prefix. -/
def lowerSixQuadraticTaylorAbelRemainder (k j : Nat) : Q' :=
  Q'.ofNat (k + 3) *
      (lowerSixWeightDriftFactor k (j + 1) +
        -lowerSixQuadraticTaylorFactor k (j + 1)) *
      lowerSixAbelCarrier (k + 1) j

theorem lowerSixQuadraticTaylorFactor_le_exact (k n : Nat) :
    lowerSixQuadraticTaylorFactor k n ≤
      lowerSixWeightDriftFactor k n := by
  unfold lowerSixQuadraticTaylorFactor
  exact lowerSixWeightDriftFloor_add_quadratic_le_factor k n

theorem lowerSixQuadraticTaylorFactorRemainder_nonnegative (k n : Nat) :
    (0 : Q') ≤ lowerSixWeightDriftFactor k n +
      -lowerSixQuadraticTaylorFactor k n := by
  exact Q'.sub_nonneg_of_le (lowerSixQuadraticTaylorFactor_le_exact k n)

/-- At mode one the quadratic Taylor factor is exact: the quadratic
coefficient vanishes and the exponent is one. -/
theorem lowerSixQuadraticTaylorFactor_exact_mode_one (k : Nat) :
    lowerSixQuadraticTaylorFactor k 1 ≈
      lowerSixWeightDriftFactor k 1 := by
  let u := unit (driftDen k) (driftDen_pos k)
  have hr := HarmonicWeightedAbelReserve.driftRatio_eqv_one_add_unitDen k
  have hbase : driftRatio k * driftRatio k ≈
      (1 : Q') + lowerSixDriftExcess k := by
    refine Q'.eqv_trans _ (((1 : Q') + u) * ((1 : Q') + u)) _ ?_ ?_
    · exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hr)
        (Q'.mul_eqv_congr_left _ _ _ hr)
    · unfold lowerSixDriftExcess
      dsimp only [u]
      taylor_flux_ring
  unfold lowerSixQuadraticTaylorFactor lowerSixWeightDriftFloor
    lowerSixWeightDriftQuadratic lowerSixQuadraticCoeff
    lowerSixWeightDriftFactor qpow
  refine Q'.eqv_trans _ ((1 : Q') + lowerSixDriftExcess k) _ ?_ ?_
  · taylor_flux_ring
  · refine Q'.eqv_trans _ (driftRatio k * driftRatio k) _
      (Q'.eqv_symm hbase) ?_
    exact Q'.eqv_symm (Q'.one_mul_eqv _)

private theorem scaled_factor_weight_algebra
    (D1 D0 W F C1 C0 : Q') :
    D1 * ((W * F) * C1) + -(D0 * (W * C0)) ≈
      W * (D1 * F * C1 + -(D0 * C0)) := by
  taylor_flux_ring

private theorem exactCarrier_eqv_taylor_add_remainder
    (D1 D0 F T C1 C0 : Q') :
    D1 * F * C1 + -(D0 * C0) ≈
      (D1 * T * C1 + -(D0 * C0)) +
        D1 * (F + -T) * C1 := by
  have hsplit : F ≈ T + (F + -T) := by
    apply Q'.eqv_symm
    refine Q'.eqv_trans _ ((T + F) + -T) _
      (Q'.eqv_symm (Q'.add_assoc_eqv T F (-T))) ?_
    refine Q'.eqv_trans _ ((F + T) + -T) _
      (Q'.add_eqv_congr_right _ _ (-T) (Q'.add_comm_eqv T F)) ?_
    refine Q'.eqv_trans _ (F + (T + -T)) _
      (Q'.add_assoc_eqv F T (-T)) ?_
    refine Q'.eqv_trans _ (F + 0) _
      (Q'.add_eqv_congr_left F _ _ (Q'.add_neg_self_eqv T)) ?_
    exact QPoly.q_add_zero_eqv F
  have hscaled : D1 * F * C1 ≈
      D1 * T * C1 + D1 * (F + -T) * C1 := by
    refine Q'.eqv_trans _ (D1 * (T + (F + -T)) * C1) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ C1
        (Q'.mul_eqv_congr_left D1 _ _ hsplit)
    · refine Q'.eqv_trans _
        ((D1 * T + D1 * (F + -T)) * C1) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ C1
          (Q'.mul_add_eqv D1 T (F + -T))
      · exact Q'.add_mul_eqv (D1 * T) (D1 * (F + -T)) C1
  refine Q'.eqv_trans _
    ((D1 * T * C1 + D1 * (F + -T) * C1) + -(D0 * C0)) _
    (Q'.add_eqv_congr_right _ _ _ hscaled) ?_
  let X := D1 * T * C1
  let Y := D1 * (F + -T) * C1
  let Z := -(D0 * C0)
  change (X + Y) + Z ≈ (X + Z) + Y
  refine Q'.eqv_trans _ (X + (Y + Z)) _
    (Q'.add_assoc_eqv X Y Z) ?_
  refine Q'.eqv_trans _ (X + (Z + Y)) _
    (Q'.add_eqv_congr_left X _ _ (Q'.add_comm_eqv Y Z)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv X Z Y)

/-- Exact factorization at every Abel index, including the augmented first
cell.  This is the finite-dimensional correction omitted by a formal
all-mode Taylor extrapolation. -/
theorem lowerSixScaledCrossTerm_eqv_taylor_add_remainder (k j : Nat) :
    lowerSixScaledCrossTerm k j ≈
      lowerSixAbelWeight k j *
        (lowerSixQuadraticTaylorAbelCarrier k j +
          lowerSixQuadraticTaylorAbelRemainder k j) := by
  let W := lowerSixAbelWeight k j
  let F := lowerSixWeightDriftFactor k (j + 1)
  let T := lowerSixQuadraticTaylorFactor k (j + 1)
  let C1 := lowerSixAbelCarrier (k + 1) j
  let C0 := lowerSixAbelCarrier k j
  let D1 := Q'.ofNat (k + 3)
  let D0 := Q'.ofNat (k + 2)
  have hw : lowerSixAbelWeight (k + 1) j ≈ W * F := by
    unfold lowerSixAbelWeight
    dsimp only [W, F]
    exact lowerSixModeWeight_step_eqv k (j + 1)
  unfold lowerSixScaledCrossTerm lowerSixWeightedAbelTerm
    lowerSixQuadraticTaylorAbelCarrier
    lowerSixQuadraticTaylorAbelRemainder
  refine Q'.eqv_trans _
    (Q'.ofNat (k + 3) *
        (lowerSixAbelWeight (k + 1) j * lowerSixAbelCarrier (k + 1) j) +
      -(Q'.ofNat (k + 2) *
        (lowerSixAbelWeight k j * lowerSixAbelCarrier k j))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _))
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)))
  · refine Q'.eqv_trans _
      (Q'.ofNat (k + 3) *
          ((lowerSixAbelWeight k j * lowerSixWeightDriftFactor k (j + 1)) *
            lowerSixAbelCarrier (k + 1) j) +
        -(Q'.ofNat (k + 2) *
          (lowerSixAbelWeight k j * lowerSixAbelCarrier k j))) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat (k + 3)) _ _
          (Q'.mul_eqv_congr_right _ _ _ hw))
    · refine Q'.eqv_trans _
        (lowerSixAbelWeight k j *
          (Q'.ofNat (k + 3) * lowerSixWeightDriftFactor k (j + 1) *
              lowerSixAbelCarrier (k + 1) j +
            -(Q'.ofNat (k + 2) * lowerSixAbelCarrier k j))) _
        (scaled_factor_weight_algebra _ _ _ _ _ _) ?_
      exact Q'.mul_eqv_congr_left _ _ _
        (exactCarrier_eqv_taylor_add_remainder _ _ _ _ _ _)

/-- Where the next Abel carrier is nonnegative, the exact prefix correction
has the expected nonnegative sign.  Hence only the adverse carrier band
requires analytic payment. -/
theorem lowerSixQuadraticTaylorAbelRemainder_nonnegative
    {k j : Nat} (hcarrier : (0 : Q') ≤ lowerSixAbelCarrier (k + 1) j) :
    (0 : Q') ≤ lowerSixQuadraticTaylorAbelRemainder k j := by
  unfold lowerSixQuadraticTaylorAbelRemainder
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
      (lowerSixQuadraticTaylorFactorRemainder_nonnegative k (j + 1)))
    hcarrier

/-- The augmented Abel endpoint contributes no exact-minus-Taylor
correction; the prefix correction starts with ordinary mode two. -/
theorem lowerSixQuadraticTaylorAbelRemainder_zero_eqv (k : Nat) :
    lowerSixQuadraticTaylorAbelRemainder k 0 ≈ 0 := by
  have hf := lowerSixQuadraticTaylorFactor_exact_mode_one k
  have hdiff : lowerSixWeightDriftFactor k 1 +
      -lowerSixQuadraticTaylorFactor k 1 ≈ 0 := by
    refine Q'.eqv_trans _
      (lowerSixQuadraticTaylorFactor k 1 +
        -lowerSixQuadraticTaylorFactor k 1) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hf)
    · exact Q'.add_neg_self_eqv _
  unfold lowerSixQuadraticTaylorAbelRemainder
  have hscaled :
      Q'.ofNat (k + 3) *
          (lowerSixWeightDriftFactor k 1 +
            -lowerSixQuadraticTaylorFactor k 1) *
            lowerSixAbelCarrier (k + 1) 0 ≈
        Q'.ofNat (k + 3) * 0 * lowerSixAbelCarrier (k + 1) 0 :=
    Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hdiff)
  exact Q'.eqv_trans _ _ _ hscaled
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_zero_eqv _))
      (Q'.zero_mul_eqv _))

/-- Taylorized prefix with the augmented endpoint retained. -/
def lowerSixQuadraticTaylorPrefix (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixAbelWeight k j *
      lowerSixQuadraticTaylorAbelCarrier k j)
    (thetaWindowRight k)

/-- Exact-minus-Taylor correction on that same prefix. -/
def lowerSixQuadraticTaylorPrefixRemainder (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixAbelWeight k j *
      lowerSixQuadraticTaylorAbelRemainder k j)
    (thetaWindowRight k)

private theorem taylor_flux_finSum_eqv_congr (f g : Nat → Q') : ∀ N,
    (∀ j, j < N → f j ≈ g j) → finSum f N ≈ finSum g N
  | 0, _ => Q'.eqv_refl 0
  | N + 1, h => by
      rw [finSum_succ, finSum_succ]
      exact Q'.add_eqv_congr'
        (taylor_flux_finSum_eqv_congr f g N
          (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self N))))
        (h N (Nat.lt_succ_self N))

theorem lowerSixScaledCrossWindowPrefix_eqv_taylor_add_remainder (k : Nat) :
    lowerSixScaledCrossWindowPrefix k ≈
      lowerSixQuadraticTaylorPrefix k +
        lowerSixQuadraticTaylorPrefixRemainder k := by
  have hterm := taylor_flux_finSum_eqv_congr
    (lowerSixScaledCrossTerm k)
    (fun j =>
      lowerSixAbelWeight k j * lowerSixQuadraticTaylorAbelCarrier k j +
      lowerSixAbelWeight k j * lowerSixQuadraticTaylorAbelRemainder k j)
    (thetaWindowRight k) (fun j _ =>
      Q'.eqv_trans _
        (lowerSixAbelWeight k j *
          (lowerSixQuadraticTaylorAbelCarrier k j +
            lowerSixQuadraticTaylorAbelRemainder k j)) _
        (lowerSixScaledCrossTerm_eqv_taylor_add_remainder k j)
        (Q'.mul_add_eqv _ _ _))
  unfold lowerSixScaledCrossWindowPrefix lowerSixScaledCrossPrefix
    lowerSixQuadraticTaylorPrefix lowerSixQuadraticTaylorPrefixRemainder
  exact Q'.eqv_trans _ _ _ hterm
    (finSum_add
      (fun j => lowerSixAbelWeight k j *
        lowerSixQuadraticTaylorAbelCarrier k j)
      (fun j => lowerSixAbelWeight k j *
        lowerSixQuadraticTaylorAbelRemainder k j)
      (thetaWindowRight k))

/-- Old-weighted Taylor suffix already supplied by the linear and quadratic
drift certificates. -/
def lowerSixQuadraticTaylorSuffix (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixModeWeight k (thetaWindowRight k + 1 + j) *
      lowerSixQuadraticTaylorCarrier k
        (thetaWindowRight k + 1 + j))
    (growingAnchor k - thetaWindowRight k)

theorem linearSuffix_add_quadraticSuffix_eqv_taylorSuffix (k : Nat) :
    lowerSixScaledLinearCrossWindowSuffix k +
        lowerSixScaledQuadraticCrossWindowSuffix k ≈
      lowerSixQuadraticTaylorSuffix k := by
  let N := growingAnchor k - thetaWindowRight k
  let W := fun j => lowerSixModeWeight k (thetaWindowRight k + 1 + j)
  let L := fun j => lowerSixScaledLinearDriftCarrier k
    (thetaWindowRight k + 1 + j)
  let Q := fun j => lowerSixScaledDriftQuadratic k
    (thetaWindowRight k + 1 + j)
  let T := fun j => lowerSixQuadraticTaylorCarrier k
    (thetaWindowRight k + 1 + j)
  have hterm : ∀ j, j < N → W j * L j + W j * Q j ≈ W j * T j := by
    intro j _
    refine Q'.eqv_trans _ (W j * (L j + Q j)) _
      (Q'.eqv_symm (Q'.mul_add_eqv (W j) (L j) (Q j))) ?_
    exact Q'.mul_eqv_congr_left (W j) _ _
      (linear_add_quadratic_eqv_taylorCarrier k
        (thetaWindowRight k + 1 + j))
  have hsum := taylor_flux_finSum_eqv_congr
    (fun j => W j * L j + W j * Q j)
    (fun j => W j * T j) N hterm
  unfold lowerSixScaledLinearCrossWindowSuffix
    lowerSixScaledQuadraticCrossWindowSuffix lowerSixQuadraticTaylorSuffix
  dsimp only [N, W, L, Q, T] at hsum ⊢
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (finSum_add
        (fun j => lowerSixModeWeight k (thetaWindowRight k + 1 + j) *
          lowerSixScaledLinearDriftCarrier k
            (thetaWindowRight k + 1 + j))
        (fun j => lowerSixModeWeight k (thetaWindowRight k + 1 + j) *
          lowerSixScaledDriftQuadratic k
            (thetaWindowRight k + 1 + j))
        (growingAnchor k - thetaWindowRight k))) hsum

/-- Exact finite-dimensional normal form of the remaining payment target. -/
def lowerSixQuadraticTaylorTarget (k : Nat) : Q' :=
  (lowerSixQuadraticTaylorPrefix k + lowerSixQuadraticTaylorSuffix k) +
    lowerSixQuadraticTaylorPrefixRemainder k

theorem linearResidual_add_quadraticSuffix_eqv_taylorTarget (k : Nat) :
    lowerSixScaledLinearCrossPaymentResidual k +
        lowerSixScaledQuadraticCrossWindowSuffix k ≈
      lowerSixQuadraticTaylorTarget k := by
  have hp := lowerSixScaledCrossWindowPrefix_eqv_taylor_add_remainder k
  have hs := linearSuffix_add_quadraticSuffix_eqv_taylorSuffix k
  unfold lowerSixScaledLinearCrossPaymentResidual
    lowerSixQuadraticTaylorTarget
  refine Q'.eqv_trans _
    (lowerSixScaledCrossWindowPrefix k +
      (lowerSixScaledLinearCrossWindowSuffix k +
        lowerSixScaledQuadraticCrossWindowSuffix k)) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    ((lowerSixQuadraticTaylorPrefix k +
        lowerSixQuadraticTaylorPrefixRemainder k) +
      lowerSixQuadraticTaylorSuffix k) _
    (Q'.add_eqv_congr' hp hs) ?_
  taylor_flux_ring

theorem quadratic_payment_of_taylorTarget_nonnegative {k : Nat}
    (h : (0 : Q') ≤ lowerSixQuadraticTaylorTarget k) :
    -lowerSixScaledLinearCrossPaymentResidual k ≤
      lowerSixScaledQuadraticCrossWindowSuffix k := by
  have hsum : (0 : Q') ≤
      lowerSixScaledLinearCrossPaymentResidual k +
        lowerSixScaledQuadraticCrossWindowSuffix k :=
    Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (linearResidual_add_quadraticSuffix_eqv_taylorTarget k)))
  have hcomm := Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  have hnegneg := Q'.neg_neg_eqv
    (lowerSixScaledLinearCrossPaymentResidual k)
  have hsub : (0 : Q') ≤ lowerSixScaledQuadraticCrossWindowSuffix k +
      -(-lowerSixScaledLinearCrossPaymentResidual k) :=
    Q'.le_trans' _ _ _ hcomm
      (Q'.le_of_eqv
        (Q'.eqv_symm (Q'.add_eqv_congr_left _ _ _ hnegneg)))
  exact Q'.le_of_sub_nonneg hsub

/-! ## Reassembly as one ordinary-mode sum

The Abel prefix and physical suffix are not two independent analytic
objects.  Apart from the inserted endpoint cell, together they are exactly
the ordinary Taylor sum over every shared mode. -/

/-- The part of the first Abel cell coming from the inserted left endpoint. -/
def lowerSixQuadraticTaylorEndpointAugmentation (k : Nat) : Q' :=
  lowerSixModeWeight k 1 *
    (Q'.ofNat 4 *
      (Q'.ofNat (k + 3) * lowerSixQuadraticTaylorFactor k 1 +
        -Q'.ofNat (k + 2)))

theorem lowerSixQuadraticTaylorAbelTerm_zero_eqv (k : Nat) :
    lowerSixAbelWeight k 0 * lowerSixQuadraticTaylorAbelCarrier k 0 ≈
      lowerSixQuadraticTaylorWeightedTerm k 1 +
        lowerSixQuadraticTaylorEndpointAugmentation k := by
  unfold lowerSixAbelWeight lowerSixQuadraticTaylorAbelCarrier
    lowerSixAbelCarrier lowerSixQuadraticTaylorWeightedTerm
    lowerSixQuadraticTaylorCarrier
    lowerSixQuadraticTaylorEndpointAugmentation
  taylor_flux_ring

theorem lowerSixQuadraticTaylorAbelTerm_succ_eqv (k j : Nat) :
    lowerSixAbelWeight k (j + 1) *
        lowerSixQuadraticTaylorAbelCarrier k (j + 1) ≈
      lowerSixQuadraticTaylorWeightedTerm k (j + 2) := by
  unfold lowerSixAbelWeight lowerSixQuadraticTaylorAbelCarrier
    lowerSixAbelCarrier lowerSixQuadraticTaylorWeightedTerm
    lowerSixQuadraticTaylorCarrier
  simp only [Nat.add_comm, Nat.add_left_comm]
  exact Q'.eqv_refl _

private theorem taylor_flux_finSum_extract_first (f : Nat → Q') : ∀ n,
    finSum f (n + 1) ≈ f 0 + finSum (fun j => f (j + 1)) n
  | 0 => by
      show (0 : Q') + f 0 ≈ f 0 + 0
      exact Q'.add_comm_eqv 0 (f 0)
  | n + 1 => by
      rw [finSum_succ, finSum_succ]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (taylor_flux_finSum_extract_first f n)) ?_
      exact Q'.add_assoc_eqv _ _ _

private theorem taylor_flux_thetaWindowRight_le_anchor_same
    {k : Nat} (hk : 48 ≤ k) :
    thetaWindowRight k ≤ growingAnchor k := by
  let c := thetaWindowCenter k
  have hc : 9 ≤ c := by
    dsimp only [c]
    exact thetaWindowCenter_ge_nine (show 38 ≤ k by omega)
  have hsq : c * c ≤ thetaWindowLength k := by
    dsimp only [c, thetaWindowCenter]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have hright : thetaWindowRight k + 1 ≤ 2 * c + 1 := by
    unfold thetaWindowRight
    dsimp only [c]
    have hdiv := Nat.div_le_self (thetaWindowCenter k) 4
    omega
  have hroom : 2 * c + 1 ≤ c * c := by
    have hmul := Nat.mul_le_mul_right c (show 3 ≤ c by omega)
    have hlinear : 2 * c + 1 ≤ 3 * c := by omega
    exact Nat.le_trans hlinear (by simpa [Nat.mul_comm] using hmul)
  rw [thetaWindowLength_eq_anchor] at hsq
  omega

private theorem taylor_flux_thetaWindowRight_pos
    {k : Nat} (hk : 48 ≤ k) :
    0 < thetaWindowRight k := by
  have hc : 9 ≤ thetaWindowCenter k :=
    thetaWindowCenter_ge_nine (show 38 ≤ k by omega)
  unfold thetaWindowRight
  omega

/-- The Abel prefix is the ordinary Taylor prefix plus exactly one endpoint
augmentation. -/
theorem lowerSixQuadraticTaylorPrefix_eqv_endpoint_add_ordinary
    {k : Nat} (hk : 48 ≤ k) :
    lowerSixQuadraticTaylorPrefix k ≈
      lowerSixQuadraticTaylorEndpointAugmentation k +
        finSum
          (fun j => lowerSixQuadraticTaylorWeightedTerm k (j + 1))
          (thetaWindowRight k) := by
  let R := thetaWindowRight k
  let f := fun j => lowerSixAbelWeight k j *
    lowerSixQuadraticTaylorAbelCarrier k j
  let g := fun j => lowerSixQuadraticTaylorWeightedTerm k (j + 1)
  have hR : 0 < R := by
    dsimp only [R]
    exact taylor_flux_thetaWindowRight_pos hk
  have hcount : R = (R - 1) + 1 := by omega
  have hf := taylor_flux_finSum_extract_first f (R - 1)
  have hg := taylor_flux_finSum_extract_first g (R - 1)
  have htail : finSum (fun j => f (j + 1)) (R - 1) ≈
      finSum (fun j => g (j + 1)) (R - 1) := by
    apply taylor_flux_finSum_eqv_congr
    intro j _
    dsimp only [f, g]
    simpa [Nat.add_assoc] using
      (lowerSixQuadraticTaylorAbelTerm_succ_eqv k j)
  rw [← hcount] at hf hg
  unfold lowerSixQuadraticTaylorPrefix
  dsimp only [R, f, g] at hf hg htail ⊢
  refine Q'.eqv_trans _ _ _ hf ?_
  refine Q'.eqv_trans _
    ((lowerSixQuadraticTaylorWeightedTerm k 1 +
        lowerSixQuadraticTaylorEndpointAugmentation k) +
      finSum
        (fun j => lowerSixQuadraticTaylorWeightedTerm k (j + 1 + 1))
        (thetaWindowRight k - 1)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (lowerSixQuadraticTaylorAbelTerm_zero_eqv k) htail
  · refine Q'.eqv_trans _
      (lowerSixQuadraticTaylorEndpointAugmentation k +
        (lowerSixQuadraticTaylorWeightedTerm k 1 +
          finSum
            (fun j => lowerSixQuadraticTaylorWeightedTerm k (j + 1 + 1))
            (thetaWindowRight k - 1))) _ ?_ ?_
    · taylor_flux_ring
    · exact Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm hg)

/-- Prefix and suffix reassemble into the complete ordinary Taylor sum, with
the endpoint augmentation kept separately. -/
theorem lowerSixQuadraticTaylorPrefix_add_suffix_eqv_endpoint_add_finSum
    {k : Nat} (hk : 48 ≤ k) :
    lowerSixQuadraticTaylorPrefix k + lowerSixQuadraticTaylorSuffix k ≈
      lowerSixQuadraticTaylorEndpointAugmentation k +
        finSum
          (fun j => lowerSixQuadraticTaylorWeightedTerm k (j + 1))
          (growingAnchor k) := by
  let R := thetaWindowRight k
  let A := growingAnchor k
  let g := fun j => lowerSixQuadraticTaylorWeightedTerm k (j + 1)
  have hRA : R ≤ A := by
    dsimp only [R, A]
    exact taylor_flux_thetaWindowRight_le_anchor_same hk
  have hcount : A = R + (A - R) := by omega
  have hsplit := finSum_split g R (A - R)
  rw [← hcount] at hsplit
  have hsuffix : lowerSixQuadraticTaylorSuffix k ≈
      finSum (fun j => g (R + j)) (A - R) := by
    apply taylor_flux_finSum_eqv_congr
    intro j _
    dsimp only [g, R, A]
    unfold lowerSixQuadraticTaylorWeightedTerm
    simp only [Nat.add_comm, Nat.add_left_comm]
    exact Q'.eqv_refl _
  have hp := lowerSixQuadraticTaylorPrefix_eqv_endpoint_add_ordinary hk
  dsimp only [R, A, g] at hsplit hsuffix
  refine Q'.eqv_trans _
    ((lowerSixQuadraticTaylorEndpointAugmentation k +
        finSum
          (fun j => lowerSixQuadraticTaylorWeightedTerm k (j + 1))
          (thetaWindowRight k)) +
      finSum
        (fun j => lowerSixQuadraticTaylorWeightedTerm k
          (thetaWindowRight k + j + 1))
        (growingAnchor k - thetaWindowRight k)) _ ?_ ?_
  · exact Q'.add_eqv_congr' hp hsuffix
  · refine Q'.eqv_trans _
      (lowerSixQuadraticTaylorEndpointAugmentation k +
        (finSum
            (fun j => lowerSixQuadraticTaylorWeightedTerm k (j + 1))
            (thetaWindowRight k) +
          finSum
            (fun j => lowerSixQuadraticTaylorWeightedTerm k
              (thetaWindowRight k + j + 1))
            (growingAnchor k - thetaWindowRight k))) _
      (Q'.add_assoc_eqv _ _ _) ?_
    exact Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm hsplit)

/-- Exact target normal form to which the finite Hermite telescope applies. -/
theorem lowerSixQuadraticTaylorTarget_eqv_endpoint_add_finSum_add_remainder
    {k : Nat} (hk : 48 ≤ k) :
    lowerSixQuadraticTaylorTarget k ≈
      (lowerSixQuadraticTaylorEndpointAugmentation k +
        finSum
          (fun j => lowerSixQuadraticTaylorWeightedTerm k (j + 1))
          (growingAnchor k)) +
        lowerSixQuadraticTaylorPrefixRemainder k := by
  unfold lowerSixQuadraticTaylorTarget
  exact Q'.add_eqv_congr_right _ _ _
    (lowerSixQuadraticTaylorPrefix_add_suffix_eqv_endpoint_add_finSum hk)

/-- Directly aligning the first adverse prefix cell with the first quadratic
suffix cell is already false at the induction anchor. -/
theorem first_aligned_quadratic_pair_fails_k247 :
    ¬ ((0 : Q') ≤
      lowerSixScaledCrossTerm 247 8 +
        lowerSixModeWeight 247 (thetaWindowRight 247 + 1) *
          lowerSixScaledDriftQuadratic 247
            (thetaWindowRight 247 + 1)) := by
  unfold lowerSixScaledCrossTerm lowerSixWeightedAbelTerm
    lowerSixAbelCarrier lowerSixAbelWeight lowerSixModeCarrier
    lowerSixModeWeight lowerSixDirichletProfile thetaRootSlope
    lowerSixScaledDriftQuadratic lowerSixWeightDriftQuadratic
    lowerSixQuadraticCoeff lowerSixDriftExcess thetaWindowRight
    thetaWindowCenter thetaWindowLength driftDen harmW harmU oneSub unit qpow
  decide

/-! ## Exact Hermite-flux skeleton

Put `D = k+2`, `h = D^{-1/2}`, and `y = n h`.  The following exact
polynomial identities identify the cancellations retained by the finite
discrete flux below. -/

def hermiteLeadingDensity (y : Q') : Q' :=
  Q'.ofNat 32 * RingNormaliser.qpow y 6 +
    -(Q'.ofNat 72 * RingNormaliser.qpow y 4) +
    Q'.ofNat 8 * RingNormaliser.qpow y 2 + 4

def hermiteLeadingFlux (y : Q') : Q' :=
  Q'.ofNat 8 * y + Q'.ofNat 16 * RingNormaliser.qpow y 3 +
    -(Q'.ofNat 16 * RingNormaliser.qpow y 5)

def hermiteLeadingFluxDerivative (y : Q') : Q' :=
  Q'.ofNat 8 + Q'.ofNat 48 * RingNormaliser.qpow y 2 +
    -(Q'.ofNat 80 * RingNormaliser.qpow y 4)

private abbrev PE := RingNormaliser.PolyExpr
private def pc (n : Int) : PE := .const n
private def pv : PE := .var 0
private def padd (a b : PE) : PE := .add a b
private def pmul (a b : PE) : PE := .mul a b
private def pneg (a : PE) : PE := .neg a
private def ppow (a : PE) (n : Nat) : PE := .pow a n

private def pHermiteLeadingDensity : PE :=
  padd (padd (padd
    (pmul (pc 32) (ppow pv 6))
    (pneg (pmul (pc 72) (ppow pv 4))))
    (pmul (pc 8) (ppow pv 2))) (pc 4)

private def pHermiteLeadingFlux : PE :=
  padd (padd (pmul (pc 8) pv)
    (pmul (pc 16) (ppow pv 3)))
    (pneg (pmul (pc 16) (ppow pv 5)))

private def pHermiteLeadingFluxDerivative : PE :=
  padd (padd (pc 8) (pmul (pc 48) (ppow pv 2)))
    (pneg (pmul (pc 80) (ppow pv 4)))

private def pHermiteLeadingL : PE :=
  pmul (pc 2) pHermiteLeadingDensity

private def pHermiteLeadingR : PE :=
  padd pHermiteLeadingFluxDerivative
    (pneg (pmul (pmul (pc 4) pv) pHermiteLeadingFlux))

private theorem pHermiteLeading_normal :
    RingNormaliser.normalize pHermiteLeadingL =
      RingNormaliser.normalize pHermiteLeadingR := by decide

/-- `2 H0` is an exact Gaussian-weighted formal derivative. -/
theorem hermiteLeading_flux_identity (y : Q') :
    Q'.ofNat 2 * hermiteLeadingDensity y ≈
      hermiteLeadingFluxDerivative y +
        -(Q'.ofNat 4 * y * hermiteLeadingFlux y) := by
  simpa [pHermiteLeadingL, pHermiteLeadingR,
    pHermiteLeadingDensity, pHermiteLeadingFlux,
    pHermiteLeadingFluxDerivative, pc, pv, padd, pmul, pneg, ppow,
    hermiteLeadingDensity, hermiteLeadingFlux,
    hermiteLeadingFluxDerivative, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pHermiteLeadingL pHermiteLeadingR pHermiteLeading_normal
      (fun _ => y))

def hermiteFirstDensity (y : Q') : Q' :=
  -(Q'.ofNat 64 * RingNormaliser.qpow y 7) +
    Q'.ofNat 192 * RingNormaliser.qpow y 5 +
    -(Q'.ofNat 112 * RingNormaliser.qpow y 3)

def hermiteFirstFlux (y : Q') : Q' :=
  Q'.ofNat 16 * RingNormaliser.qpow y 6 +
    -(Q'.ofNat 24 * RingNormaliser.qpow y 4) +
    Q'.ofNat 4 * RingNormaliser.qpow y 2 + 2

def hermiteFirstFluxDerivative (y : Q') : Q' :=
  Q'.ofNat 96 * RingNormaliser.qpow y 5 +
    -(Q'.ofNat 96 * RingNormaliser.qpow y 3) +
    Q'.ofNat 8 * y

private def pHermiteFirstDensity : PE :=
  padd (padd
    (pneg (pmul (pc 64) (ppow pv 7)))
    (pmul (pc 192) (ppow pv 5)))
    (pneg (pmul (pc 112) (ppow pv 3)))

private def pHermiteFirstFlux : PE :=
  padd (padd (padd
    (pmul (pc 16) (ppow pv 6))
    (pneg (pmul (pc 24) (ppow pv 4))))
    (pmul (pc 4) (ppow pv 2))) (pc 2)

private def pHermiteFirstFluxDerivative : PE :=
  padd (padd
    (pmul (pc 96) (ppow pv 5))
    (pneg (pmul (pc 96) (ppow pv 3))))
    (pmul (pc 8) pv)

private def pHermiteFirstR : PE :=
  padd pHermiteFirstFluxDerivative
    (pneg (pmul (pmul (pc 4) pv) pHermiteFirstFlux))

private theorem pHermiteFirst_normal :
    RingNormaliser.normalize pHermiteFirstDensity =
      RingNormaliser.normalize pHermiteFirstR := by decide

/-- The first correction is another exact Gaussian flux. -/
theorem hermiteFirst_flux_identity (y : Q') :
    hermiteFirstDensity y ≈
      hermiteFirstFluxDerivative y +
        -(Q'.ofNat 4 * y * hermiteFirstFlux y) := by
  simpa [pHermiteFirstDensity, pHermiteFirstR, pHermiteFirstFlux,
    pHermiteFirstFluxDerivative, pc, pv, padd, pmul, pneg, ppow,
    hermiteFirstDensity, hermiteFirstFlux,
    hermiteFirstFluxDerivative, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pHermiteFirstDensity pHermiteFirstR pHermiteFirst_normal
      (fun _ => y))

/-- The second correction after clearing its coefficient denominator. -/
def hermiteSecondClearedDensity (y : Q') : Q' :=
  Q'.ofNat 1792 * RingNormaliser.qpow y 8 +
    -(Q'.ofNat 8192 * RingNormaliser.qpow y 6) +
    Q'.ofNat 9152 * RingNormaliser.qpow y 4 +
    -(Q'.ofNat 2112 * RingNormaliser.qpow y 2)

def hermiteSecondFlux (y : Q') : Q' :=
  -(Q'.ofNat 448 * RingNormaliser.qpow y 7) +
    Q'.ofNat 1264 * RingNormaliser.qpow y 5 +
    -(Q'.ofNat 708 * RingNormaliser.qpow y 3) +
    -(Q'.ofNat 3 * y)

def hermiteSecondFluxDerivative (y : Q') : Q' :=
  -(Q'.ofNat 3136 * RingNormaliser.qpow y 6) +
    Q'.ofNat 6320 * RingNormaliser.qpow y 4 +
    -(Q'.ofNat 2124 * RingNormaliser.qpow y 2) +
    -(Q'.ofNat 3)

private def pHermiteSecondDensity : PE :=
  padd (padd (padd
    (pmul (pc 1792) (ppow pv 8))
    (pneg (pmul (pc 8192) (ppow pv 6))))
    (pmul (pc 9152) (ppow pv 4)))
    (pneg (pmul (pc 2112) (ppow pv 2)))

private def pHermiteSecondFlux : PE :=
  padd (padd (padd
    (pneg (pmul (pc 448) (ppow pv 7)))
    (pmul (pc 1264) (ppow pv 5)))
    (pneg (pmul (pc 708) (ppow pv 3))))
    (pneg (pmul (pc 3) pv))

private def pHermiteSecondFluxDerivative : PE :=
  padd (padd (padd
    (pneg (pmul (pc 3136) (ppow pv 6)))
    (pmul (pc 6320) (ppow pv 4)))
    (pneg (pmul (pc 2124) (ppow pv 2))))
    (pneg (pc 3))

private def pHermiteSecondR : PE :=
  padd (padd (pc 3) pHermiteSecondFluxDerivative)
    (pneg (pmul (pmul (pc 4) pv) pHermiteSecondFlux))

private theorem pHermiteSecond_normal :
    RingNormaliser.normalize pHermiteSecondDensity =
      RingNormaliser.normalize pHermiteSecondR := by decide

/-- The positive second-order residue is `3/24 = 1/8` Gaussian mass,
plus an exact flux. -/
theorem hermiteSecond_positive_mass_plus_flux_identity (y : Q') :
    hermiteSecondClearedDensity y ≈
      Q'.ofNat 3 + hermiteSecondFluxDerivative y +
        -(Q'.ofNat 4 * y * hermiteSecondFlux y) := by
  simpa [pHermiteSecondDensity, pHermiteSecondR, pHermiteSecondFlux,
    pHermiteSecondFluxDerivative, pc, pv, padd, pmul, pneg, ppow,
    hermiteSecondClearedDensity, hermiteSecondFlux,
    hermiteSecondFluxDerivative, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pHermiteSecondDensity pHermiteSecondR pHermiteSecond_normal
      (fun _ => y))

/-! ## Actual finite-`D` discrete flux -/

/-- Cleared modified-Hermite flux polynomial.  It is `48 D^4` times
the discrete flux through the positive `D^{-1}` Gaussian-mass order. -/
def lowerSixDiscreteHermiteFluxPoly (D N : Q') : Q' :=
  let D2 := RingNormaliser.qpow D 2
  let D3 := RingNormaliser.qpow D 3
  let D4 := RingNormaliser.qpow D 4
  let N3 := RingNormaliser.qpow N 3
  let N4 := RingNormaliser.qpow N 4
  let N5 := RingNormaliser.qpow N 5
  let N6 := RingNormaliser.qpow N 6
  let N7 := RingNormaliser.qpow N 7
  Q'.ofNat 192 * N * D4 +
    Q'.ofNat 384 * N3 * D3 +
    -(Q'.ofNat 6 * N * D3) +
    -(Q'.ofNat 384 * N5 * D2) +
    Q'.ofNat 576 * N4 * D2 +
    Q'.ofNat 184 * N3 * D2 +
    Q'.ofNat 224 * N5 * D +
    -(Q'.ofNat 256 * N7) +
    Q'.ofNat 576 * N6 +
    Q'.ofNat 3 * D3

def lowerSixDiscreteHermiteFluxNumerator (k n : Nat) : Q' :=
  lowerSixModeWeight k n *
    lowerSixDiscreteHermiteFluxPoly (Q'.ofNat (k + 2)) (Q'.ofNat n)

/-- The positive cleared `1/(8D)` Gaussian-mass term. -/
def lowerSixDiscreteHermiteMassNumerator (k n : Nat) : Q' :=
  Q'.ofNat 6 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3 *
    lowerSixModeWeight k n

/-- Exact finite-`D` remainder after subtracting the forward flux difference
and positive mass from `48 D^4` times the actual Taylor summand. -/
def lowerSixDiscreteHermiteRemainder (k n : Nat) : Q' :=
  Q'.ofNat 48 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4 *
      lowerSixQuadraticTaylorWeightedTerm k n +
    -(lowerSixDiscreteHermiteFluxNumerator k (n + 1) +
      -lowerSixDiscreteHermiteFluxNumerator k n) +
    -lowerSixDiscreteHermiteMassNumerator k n

private def pFiniteFluxL : PE := .var 0
private def pFiniteFluxR : PE :=
  .add (.add (.var 1) (.var 2))
    (.add (.add (.var 0) (.neg (.var 1))) (.neg (.var 2)))

private theorem pFiniteFlux_normal :
    RingNormaliser.normalize pFiniteFluxL =
      RingNormaliser.normalize pFiniteFluxR := by decide

private theorem finite_flux_reassemble (A B C : Q') :
    A ≈ B + C + (A + -B + -C) := by
  simpa [pFiniteFluxL, pFiniteFluxR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pFiniteFluxL pFiniteFluxR pFiniteFlux_normal
      (fun | 0 => A | 1 => B | _ => C))

/-- Exact division-free finite-`D` Hermite-flux decomposition of the actual
unified Taylor term. -/
theorem lowerSixQuadraticTaylorWeightedTerm_finite_flux (k n : Nat) :
    Q'.ofNat 48 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4 *
        lowerSixQuadraticTaylorWeightedTerm k n ≈
      (lowerSixDiscreteHermiteFluxNumerator k (n + 1) +
          -lowerSixDiscreteHermiteFluxNumerator k n) +
        lowerSixDiscreteHermiteMassNumerator k n +
        lowerSixDiscreteHermiteRemainder k n := by
  unfold lowerSixDiscreteHermiteRemainder
  exact finite_flux_reassemble _ _ _

private def pForwardDifferenceStepL : PE :=
  .add (.add (.var 0) (.neg (.var 1)))
    (.add (.var 2) (.neg (.var 0)))
private def pForwardDifferenceStepR : PE :=
  .add (.var 2) (.neg (.var 1))

private theorem pForwardDifferenceStep_normal :
    RingNormaliser.normalize pForwardDifferenceStepL =
      RingNormaliser.normalize pForwardDifferenceStepR := by decide

private theorem forwardDifference_step (x a b : Q') :
    (x + -a) + (b + -x) ≈ b + -a := by
  simpa [pForwardDifferenceStepL, pForwardDifferenceStepR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pForwardDifferenceStepL pForwardDifferenceStepR
      pForwardDifferenceStep_normal
      (fun | 0 => x | 1 => a | _ => b))

private theorem taylor_flux_finSum_forwardDifference (F : Nat → Q') : ∀ N,
    finSum (fun j => F (j + 1) + -F j) N ≈ F N + -F 0
  | 0 => Q'.eqv_symm (Q'.add_neg_self_eqv (F 0))
  | N + 1 => by
      rw [finSum_succ]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (taylor_flux_finSum_forwardDifference F N)) ?_
      exact forwardDifference_step (F N) (F 0) (F (N + 1))

/-- Finite summation leaves only two flux endpoints, positive mass, and the
summed remainder. -/
theorem lowerSixQuadraticTaylorWeightedFinSum_finite_flux (k N : Nat) :
    Q'.ofNat 48 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4 *
        finSum (fun j => lowerSixQuadraticTaylorWeightedTerm k (j + 1)) N ≈
      (lowerSixDiscreteHermiteFluxNumerator k (N + 1) +
          -lowerSixDiscreteHermiteFluxNumerator k 1) +
        finSum (fun j => lowerSixDiscreteHermiteMassNumerator k (j + 1)) N +
        finSum (fun j => lowerSixDiscreteHermiteRemainder k (j + 1)) N := by
  let C := Q'.ofNat 48 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4
  let dF := fun j => lowerSixDiscreteHermiteFluxNumerator k (j + 2) +
    -lowerSixDiscreteHermiteFluxNumerator k (j + 1)
  let M := fun j => lowerSixDiscreteHermiteMassNumerator k (j + 1)
  let R := fun j => lowerSixDiscreteHermiteRemainder k (j + 1)
  let T := fun j => lowerSixQuadraticTaylorWeightedTerm k (j + 1)
  have hpoint : ∀ j, C * T j ≈ (dF j + M j) + R j := by
    intro j
    dsimp only [C, T, dF, M, R]
    simpa [Nat.add_assoc] using
      (lowerSixQuadraticTaylorWeightedTerm_finite_flux k (j + 1))
  have hsum : finSum (fun j => C * T j) N ≈
      finSum (fun j => (dF j + M j) + R j) N :=
    RationalTail.finSum_eqv_congr _ _ hpoint N
  have hflux : finSum dF N ≈
      lowerSixDiscreteHermiteFluxNumerator k (N + 1) +
        -lowerSixDiscreteHermiteFluxNumerator k 1 := by
    simpa [dF, Nat.add_assoc] using
      (taylor_flux_finSum_forwardDifference
        (fun j => lowerSixDiscreteHermiteFluxNumerator k (j + 1)) N)
  have hdm := RationalTail.finSum_add dF M N
  have hdm' : finSum (fun j => dF j + M j) N ≈
      (lowerSixDiscreteHermiteFluxNumerator k (N + 1) +
          -lowerSixDiscreteHermiteFluxNumerator k 1) + finSum M N :=
    Q'.eqv_trans _ _ _ hdm (Q'.add_eqv_congr_right _ _ _ hflux)
  dsimp only [C, T, dF, M, R] at hsum hdm' ⊢
  refine Q'.eqv_trans _ _ _
    (RationalTail.const_mul_finSum
      (fun j => lowerSixQuadraticTaylorWeightedTerm k (j + 1))
      (Q'.ofNat 48 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4) N) ?_
  refine Q'.eqv_trans _ _ _ hsum ?_
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_add
      (fun j =>
        (lowerSixDiscreteHermiteFluxNumerator k (j + 2) +
            -lowerSixDiscreteHermiteFluxNumerator k (j + 1)) +
          lowerSixDiscreteHermiteMassNumerator k (j + 1))
      (fun j => lowerSixDiscreteHermiteRemainder k (j + 1)) N) ?_
  exact Q'.add_eqv_congr_right _ _ _ hdm'

/-- Arbitrary-start form, matching a physical suffix without reindexing it
back to mode one. -/
theorem lowerSixQuadraticTaylorWeightedFinSumFrom_finite_flux
    (k S N : Nat) :
    Q'.ofNat 48 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4 *
        finSum (fun j => lowerSixQuadraticTaylorWeightedTerm k (S + j)) N ≈
      (lowerSixDiscreteHermiteFluxNumerator k (S + N) +
          -lowerSixDiscreteHermiteFluxNumerator k S) +
        finSum (fun j => lowerSixDiscreteHermiteMassNumerator k (S + j)) N +
        finSum (fun j => lowerSixDiscreteHermiteRemainder k (S + j)) N := by
  let C := Q'.ofNat 48 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4
  let dF := fun j => lowerSixDiscreteHermiteFluxNumerator k (S + (j + 1)) +
    -lowerSixDiscreteHermiteFluxNumerator k (S + j)
  let M := fun j => lowerSixDiscreteHermiteMassNumerator k (S + j)
  let R := fun j => lowerSixDiscreteHermiteRemainder k (S + j)
  let T := fun j => lowerSixQuadraticTaylorWeightedTerm k (S + j)
  have hpoint : ∀ j, C * T j ≈ (dF j + M j) + R j := by
    intro j
    dsimp only [C, T, dF, M, R]
    simpa [Nat.add_assoc] using
      (lowerSixQuadraticTaylorWeightedTerm_finite_flux k (S + j))
  have hsum : finSum (fun j => C * T j) N ≈
      finSum (fun j => (dF j + M j) + R j) N :=
    RationalTail.finSum_eqv_congr _ _ hpoint N
  have hflux : finSum dF N ≈
      lowerSixDiscreteHermiteFluxNumerator k (S + N) +
        -lowerSixDiscreteHermiteFluxNumerator k S := by
    simpa [dF, Nat.add_assoc] using
      (taylor_flux_finSum_forwardDifference
        (fun j => lowerSixDiscreteHermiteFluxNumerator k (S + j)) N)
  have hdm := RationalTail.finSum_add dF M N
  have hdm' : finSum (fun j => dF j + M j) N ≈
      (lowerSixDiscreteHermiteFluxNumerator k (S + N) +
          -lowerSixDiscreteHermiteFluxNumerator k S) + finSum M N :=
    Q'.eqv_trans _ _ _ hdm (Q'.add_eqv_congr_right _ _ _ hflux)
  dsimp only [C, T, dF, M, R] at hsum hdm' ⊢
  refine Q'.eqv_trans _ _ _
    (RationalTail.const_mul_finSum
      (fun j => lowerSixQuadraticTaylorWeightedTerm k (S + j))
      (Q'.ofNat 48 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4) N) ?_
  refine Q'.eqv_trans _ _ _ hsum ?_
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_add
      (fun j =>
        (lowerSixDiscreteHermiteFluxNumerator k (S + (j + 1)) +
            -lowerSixDiscreteHermiteFluxNumerator k (S + j)) +
          lowerSixDiscreteHermiteMassNumerator k (S + j))
      (fun j => lowerSixDiscreteHermiteRemainder k (S + j)) N) ?_
  exact Q'.add_eqv_congr_right _ _ _ hdm'

/-- Pointwise remainder nonnegativity is false; any valid envelope must sum
the remainder. -/
theorem discreteHermiteRemainder_pointwise_nonnegative_fails_k247_n15 :
    ¬ ((0 : Q') ≤ lowerSixDiscreteHermiteRemainder 247 15) := by
  unfold lowerSixDiscreteHermiteRemainder
    lowerSixDiscreteHermiteMassNumerator
    lowerSixDiscreteHermiteFluxNumerator lowerSixDiscreteHermiteFluxPoly
    lowerSixQuadraticTaylorWeightedTerm lowerSixQuadraticTaylorCarrier
    lowerSixQuadraticTaylorFactor lowerSixWeightDriftFloor
    lowerSixWeightDriftQuadratic lowerSixQuadraticCoeff
    lowerSixDriftExcess lowerSixModeWeight lowerSixModeCarrier
    lowerSixDirichletProfile thetaRootSlope driftDen harmW harmU
    oneSub unit RingNormaliser.qpow qpow
  decide

#print axioms linear_add_quadratic_eqv_taylorCarrier
#print axioms lowerSixQuadraticTaylorFactor_le_exact
#print axioms lowerSixQuadraticTaylorFactorRemainder_nonnegative
#print axioms lowerSixQuadraticTaylorFactor_exact_mode_one
#print axioms lowerSixScaledCrossTerm_eqv_taylor_add_remainder
#print axioms lowerSixQuadraticTaylorAbelRemainder_nonnegative
#print axioms lowerSixQuadraticTaylorAbelRemainder_zero_eqv
#print axioms lowerSixScaledCrossWindowPrefix_eqv_taylor_add_remainder
#print axioms linearSuffix_add_quadraticSuffix_eqv_taylorSuffix
#print axioms linearResidual_add_quadraticSuffix_eqv_taylorTarget
#print axioms quadratic_payment_of_taylorTarget_nonnegative
#print axioms lowerSixQuadraticTaylorAbelTerm_zero_eqv
#print axioms lowerSixQuadraticTaylorAbelTerm_succ_eqv
#print axioms lowerSixQuadraticTaylorPrefix_eqv_endpoint_add_ordinary
#print axioms lowerSixQuadraticTaylorPrefix_add_suffix_eqv_endpoint_add_finSum
#print axioms lowerSixQuadraticTaylorTarget_eqv_endpoint_add_finSum_add_remainder
#print axioms first_aligned_quadratic_pair_fails_k247
#print axioms hermiteLeading_flux_identity
#print axioms hermiteFirst_flux_identity
#print axioms hermiteSecond_positive_mass_plus_flux_identity
#print axioms lowerSixQuadraticTaylorWeightedTerm_finite_flux
#print axioms lowerSixQuadraticTaylorWeightedFinSum_finite_flux
#print axioms lowerSixQuadraticTaylorWeightedFinSumFrom_finite_flux
#print axioms discreteHermiteRemainder_pointwise_nonnegative_fails_k247_n15

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
