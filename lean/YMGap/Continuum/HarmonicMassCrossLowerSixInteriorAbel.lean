/-
Exact Abel coordinates for the boundary-free lower-six interior residual.

Every signed Dirichlet cell is a positive squared-base weight times an
explicit slope carrier.  The left endpoint payment is folded into the first
carrier, so the complete remaining residual is one finite weighted sum.  A
constructive summation-by-parts identity then exposes its prefix excursions.

The ordinary one-sided prefix criterion is also fenced: its ninth prefix is
strictly negative already at the first symbolic scale `k=48`.  Thus the exact
identity is useful, but closure must retain compensation from the right tail
(for example through a two-sided window or paired-cell certificate).
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixTerminalPayment

namespace YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixTerminalPayment
open YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem interior_abel_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "interior_abel_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               interior_abel_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- The polynomial carrier left after removing the positive squared-base
weight from a lower-six Dirichlet cell. -/
def lowerSixModeCarrier (k n : Nat) : Q' :=
  Q'.ofNat 4 * (thetaRootSlope k n * thetaRootSlope k n) +
    -(lowerSixDirichletProfile k * Q'.ofNat (n * n))

/-- The exact positive weight of mode `n`. -/
def lowerSixModeWeight (k n : Nat) : Q' :=
  qpow (harmW k * harmW k) (n * n)

/-- Exact mode factorization of every signed lower-six cell. -/
theorem lowerSixDirichletIncrement_mode_factor (k n : Nat) :
    lowerSixDirichletIncrement k n ≈
      lowerSixModeWeight k n * lowerSixModeCarrier k n := by
  have hd := thetaDirichletCell_slope_factor k n
  unfold lowerSixDirichletIncrement integerThetaTerm
  unfold lowerSixModeWeight lowerSixModeCarrier
  refine Q'.eqv_trans _
    (Q'.ofNat 4 *
        (qpow (harmW k * harmW k) (n * n) *
          (thetaRootSlope k n * thetaRootSlope k n)) +
      -(lowerSixDirichletProfile k *
        (Q'.ofNat (n * n) *
          qpow (harmW k * harmW k) (n * n)))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _ hd)
      (Q'.eqv_refl _)
  · interior_abel_ring

/-- Abel carrier indexed from zero.  The left endpoint is inserted into the
first carrier because its weight is exactly the first mode weight. -/
def lowerSixAbelCarrier (k : Nat) : Nat → Q'
  | 0 => lowerSixModeCarrier k 1 + Q'.ofNat 4
  | j + 1 => lowerSixModeCarrier k (j + 2)

/-- Abel weight indexed from zero. -/
def lowerSixAbelWeight (k j : Nat) : Q' :=
  lowerSixModeWeight k (j + 1)

/-- The corresponding physical term sequence, with the left endpoint folded
into its first entry. -/
def lowerSixAugmentedIncrement (k : Nat) : Nat → Q'
  | 0 => lowerSixDirichletIncrement k 1 +
      Q'.ofNat 4 * integerThetaTerm (harmW k) 1
  | j + 1 => lowerSixDirichletIncrement k (j + 2)

theorem lowerSixAbel_term_eqv (k j : Nat) :
    lowerSixAbelCarrier k j * lowerSixAbelWeight k j ≈
      lowerSixAugmentedIncrement k j := by
  cases j with
  | zero =>
      have hf := lowerSixDirichletIncrement_mode_factor k 1
      unfold lowerSixAbelCarrier lowerSixAbelWeight
        lowerSixAugmentedIncrement lowerSixModeWeight integerThetaTerm
      refine Q'.eqv_trans _
        (lowerSixModeWeight k 1 * lowerSixModeCarrier k 1 +
          Q'.ofNat 4 *
            (Q'.ofNat (1 * 1) *
              qpow (harmW k * harmW k) (1 * 1))) _ ?_ ?_
      · unfold lowerSixModeWeight
        interior_abel_ring
      · exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hf)
  | succ j =>
      simp only [lowerSixAbelCarrier, lowerSixAbelWeight,
        lowerSixAugmentedIncrement, Nat.add_assoc]
      change lowerSixModeCarrier k (j + 2) *
          lowerSixModeWeight k (j + 2) ≈
        lowerSixDirichletIncrement k (j + 2)
      exact Q'.eqv_trans _
        (lowerSixModeWeight k (j + 2) *
          lowerSixModeCarrier k (j + 2)) _
        (Q'.mul_comm_eqv _ _)
        (Q'.eqv_symm
          (lowerSixDirichletIncrement_mode_factor k (j + 2)))

private theorem lowerSixAugmented_finSum (k : Nat) : ∀ N,
    finSum (lowerSixAugmentedIncrement k) (N + 1) ≈
      finSum (fun j => lowerSixDirichletIncrement k (j + 1)) (N + 1) +
        Q'.ofNat 4 * integerThetaTerm (harmW k) 1
  | 0 => by
      simp only [finSum_succ, finSum_zero, lowerSixAugmentedIncrement,
        Q'.zero_add']
      exact Q'.eqv_refl _
  | N + 1 => by
      change
        (finSum (lowerSixAugmentedIncrement k) (N + 1) +
            lowerSixDirichletIncrement k (N + 2)) ≈
          ((finSum (fun j => lowerSixDirichletIncrement k (j + 1))
              (N + 1) + lowerSixDirichletIncrement k (N + 2)) +
            Q'.ofNat 4 * integerThetaTerm (harmW k) 1)
      refine Q'.eqv_trans _
        ((finSum (fun j => lowerSixDirichletIncrement k (j + 1))
              (N + 1) +
            Q'.ofNat 4 * integerThetaTerm (harmW k) 1) +
          lowerSixDirichletIncrement k (N + 2)) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _
          (lowerSixAugmented_finSum k N)
      · interior_abel_ring

/-- The complete boundary-free residual is exactly one weighted carrier sum.
No endpoint or truncation loss remains outside this expression. -/
theorem lowerSixInterior_eqv_weightedAbel (k : Nat) :
    lowerSixInteriorSum k +
        Q'.ofNat 4 * integerThetaTerm (harmW k) 1 ≈
      finSum (fun j => lowerSixAbelCarrier k j * lowerSixAbelWeight k j)
        (growingAnchor k) := by
  have hanchor : growingAnchor k = (2 * k + 3) + 1 := by
    unfold growingAnchor
    omega
  rw [hanchor]
  refine Q'.eqv_symm (Q'.eqv_trans _
    (finSum (lowerSixAugmentedIncrement k) ((2 * k + 3) + 1)) _ ?_ ?_)
  · exact finSum_eqv_congr
      (fun j => lowerSixAbelCarrier k j * lowerSixAbelWeight k j)
      (lowerSixAugmentedIncrement k)
      (lowerSixAbel_term_eqv k) ((2 * k + 3) + 1)
  · unfold lowerSixInteriorSum
    rw [hanchor]
    exact lowerSixAugmented_finSum k (2 * k + 3)

/-- Exact constructive summation by parts for the remaining residual.  This
is an identity, with no sign assumptions on either prefixes or differences. -/
theorem lowerSixInterior_finite_abel (k : Nat) :
    lowerSixInteriorSum k +
        Q'.ofNat 4 * integerThetaTerm (harmW k) 1 ≈
      abelPrefix (lowerSixAbelCarrier k) (2 * k + 3) *
          lowerSixAbelWeight k (2 * k + 3) +
        abelIncrementSum (lowerSixAbelCarrier k) (lowerSixAbelWeight k)
          (2 * k + 3) := by
  refine Q'.eqv_trans _
    (finSum (fun j => lowerSixAbelCarrier k j * lowerSixAbelWeight k j)
      (growingAnchor k)) _ (lowerSixInterior_eqv_weightedAbel k) ?_
  have hanchor : growingAnchor k = (2 * k + 3) + 1 := by
    unfold growingAnchor
    omega
  rw [hanchor, ← MovingCutoff.fsum_eq_finSum]
  exact finite_abel (lowerSixAbelCarrier k) (lowerSixAbelWeight k)
    (2 * k + 3)

/-- Ordinary one-sided Abel prefixes cannot close the symbolic range: the
ninth augmented carrier prefix is already strictly negative at `k=48`. -/
theorem lowerSix_plainAbelPrefix_fails_k48 :
    ¬ ((0 : Q') ≤ abelPrefix (lowerSixAbelCarrier 48) 8) := by
  unfold abelPrefix lowerSixAbelCarrier lowerSixModeCarrier
    lowerSixDirichletProfile thetaRootSlope harmW harmU
    ReciprocalBernoulliUpper.oneSub unit qpow fsum
  decide

#print axioms lowerSixDirichletIncrement_mode_factor
#print axioms lowerSixAbel_term_eqv
#print axioms lowerSixInterior_eqv_weightedAbel
#print axioms lowerSixInterior_finite_abel
#print axioms lowerSix_plainAbelPrefix_fails_k48

end YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
