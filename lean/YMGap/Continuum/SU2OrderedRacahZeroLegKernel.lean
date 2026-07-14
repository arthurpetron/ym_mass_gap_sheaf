/-
# Symbolic unit Racah kernel on the zero-first-leg family

For the physical tetrahedron

  `{0,b,b; c,b+c-2p,b+c-2p}`,

the Racah `t`-sum has exactly one supported term, at `t=b+c-p`.  This file
collapses that term and performs the complete factorial cancellation proving
that the dimension-absorbed squared kernel is exactly one for every
`p ≤ min b c`.
-/

import YMGap.Continuum.SU2OrderedRacahZeroLegFamily
import YMGap.Continuum.FusionBratteli

namespace YMGap.Continuum.SU2OrderedRacahZeroLegKernel

set_option maxHeartbeats 2000000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.TreeGraphBoundProgress
open YMGap.Continuum.SixJKernel
open YMGap.Continuum.SU2OrderedRacahMultiplicityFence
open YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier
open YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier
open YMGap.Continuum.SU2OrderedRacahZeroLegFamily
open YMGap.Continuum.SU2TransvectantClosedBinaryGram
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted

local infix:50 " ≈ " => Q'.eqv

def zeroLegD (b c p : Nat) : Nat := b + c - 2 * p
def zeroLegT (b c p : Nat) : Nat := b + c - p
def zeroLegDen (b c p : Nat) : Nat := fact (c - p) * fact p * fact (b - p)

def zeroLegRacahAmplitude (b c p : Nat) : Q' :=
  let T := zeroLegT b c p
  ⟨(if T % 2 = 0 then (1 : Int) else -1) * Int.ofNat (fact (T + 1)),
    zeroLegDen b c p - 1⟩

/-! ## Exact triangle/parity guard -/

theorem zero_leg_valid6 (b c p : Nat) (hp : p ≤ min b c) :
    valid6 0 b c (zeroLegD b c p) b (zeroLegD b c p) = true := by
  have hp' := Nat.le_min.mp hp
  have h0b : fusionOK 0 b b = true :=
    (fusionOK_iff_ladder 0 b b).2 ⟨0, by omega, by omega, by omega⟩
  have h0d : fusionOK 0 (zeroLegD b c p) (zeroLegD b c p) = true :=
    (fusionOK_iff_ladder 0 (zeroLegD b c p) (zeroLegD b c p)).2
      ⟨0, by omega, by omega, by omega⟩
  have hcbd : fusionOK c b (zeroLegD b c p) = true :=
    (fusionOK_iff_ladder c b (zeroLegD b c p)).2
      ⟨p, hp'.2, hp'.1, by unfold zeroLegD; omega⟩
  have hcdb : fusionOK c (zeroLegD b c p) b = true :=
    (fusionOK_iff_ladder c (zeroLegD b c p) b).2
      ⟨c - p, by omega, by unfold zeroLegD; omega,
        by unfold zeroLegD; omega⟩
  unfold valid6
  simp only [h0b, h0d, hcbd, hcdb, Bool.true_and]

/-! ## The one supported Racah term -/

private theorem zero_leg_racah_parameters (b c p : Nat) (hp : p ≤ min b c) :
    (0 + b + b) / 2 = b ∧
    (0 + zeroLegD b c p + zeroLegD b c p) / 2 = zeroLegD b c p ∧
    (c + b + zeroLegD b c p) / 2 = zeroLegT b c p ∧
    (c + zeroLegD b c p + b) / 2 = zeroLegT b c p ∧
    (0 + b + c + zeroLegD b c p) / 2 = zeroLegT b c p ∧
    (b + b + zeroLegD b c p + zeroLegD b c p) / 2 =
      b + zeroLegD b c p ∧
    (0 + b + c + zeroLegD b c p) / 2 = zeroLegT b c p := by
  have hp' := Nat.le_min.mp hp
  unfold zeroLegD zeroLegT
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

private theorem zero_leg_tGuard_at_T (b c p : Nat) (hp : p ≤ min b c) :
    tGuard b (zeroLegD b c p) (zeroLegT b c p) (zeroLegT b c p)
      (zeroLegT b c p) (b + zeroLegD b c p) (zeroLegT b c p)
      (zeroLegT b c p) = true := by
  have hp' := Nat.le_min.mp hp
  unfold tGuard zeroLegD zeroLegT
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  exact ⟨by omega, by omega⟩

theorem zero_leg_racahSummand_onehot (b c p t : Nat)
    (hp : p ≤ min b c) :
    racahSummand
      ((0 + b + b) / 2)
      ((0 + zeroLegD b c p + zeroLegD b c p) / 2)
      ((c + b + zeroLegD b c p) / 2)
      ((c + zeroLegD b c p + b) / 2)
      ((0 + b + c + zeroLegD b c p) / 2)
      ((b + b + zeroLegD b c p + zeroLegD b c p) / 2)
      ((0 + b + c + zeroLegD b c p) / 2) t ≈
      (if t = zeroLegT b c p then zeroLegRacahAmplitude b c p else 0) := by
  have hpar := zero_leg_racah_parameters b c p hp
  rw [hpar.1, hpar.2.1, hpar.2.2.1, hpar.2.2.2.1,
    hpar.2.2.2.2.1, hpar.2.2.2.2.2.1]
  by_cases ht : t = zeroLegT b c p
  · subst t
    rw [if_pos rfl]
    unfold racahSummand
    rw [if_pos (zero_leg_tGuard_at_T b c p hp)]
    have h1 : zeroLegT b c p - b = c - p := by
      unfold zeroLegT
      omega
    have h2 : zeroLegT b c p - zeroLegD b c p = p := by
      unfold zeroLegT zeroLegD
      omega
    have h3 : b + zeroLegD b c p - zeroLegT b c p = b - p := by
      unfold zeroLegT zeroLegD
      omega
    unfold zeroLegRacahAmplitude zeroLegDen sevenFacts
    have hp' := Nat.le_min.mp hp
    simp only [Nat.sub_self, fact, Nat.mul_one]
    rw [h1, h2, h3]
    exact Q'.eqv_refl _
  · rw [if_neg ht]
    unfold racahSummand
    rw [if_neg]
    · exact Q'.eqv_refl 0
    · intro hg
      unfold tGuard at hg
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      exact ht (by omega)

theorem zero_leg_racahSum_eq_amplitude (b c p : Nat)
    (hp : p ≤ min b c) :
    racahSum 0 b b c (zeroLegD b c p) (zeroLegD b c p) ≈
      zeroLegRacahAmplitude b c p := by
  unfold racahSum
  have hcongr := finSum_eqv_congr _ _
    (fun t => zero_leg_racahSummand_onehot b c p t hp)
    ((0 + b + b + c + zeroLegD b c p + zeroLegD b c p) / 2 + 1)
  have hinside : zeroLegT b c p <
      (0 + b + b + c + zeroLegD b c p + zeroLegD b c p) / 2 + 1 := by
    have hp' := Nat.le_min.mp hp
    unfold zeroLegT zeroLegD
    omega
  exact Q'.eqv_trans _ _ _ hcongr
    (YMGap.Continuum.SU2TransvectantGeneralCoefficient.finSum_onehot_value
      (zeroLegRacahAmplitude b c p)
      ((0 + b + b + c + zeroLegD b c p + zeroLegD b c p) / 2 + 1)
      (zeroLegT b c p) hinside)

/-! ## Factorial cancellation -/

private theorem mkN_den_of_pred (n d : Nat) (hd : 0 < d) :
    (Q'.mkN n (d - 1)).den = d := by
  change d - 1 + 1 = d
  omega

private theorem signed_den_of_pred (z : Int) (d : Nat) (hd : 0 < d) :
    ((⟨z, d - 1⟩ : Q').den) = d := by
  change d - 1 + 1 = d
  omega

theorem zero_leg_triSq_zero (n : Nat) :
    triSq 0 n n = Q'.mkN (fact n) (fact (n + 1) - 1) := by
  unfold triSq triSqNum triSqDen
  simp only [Nat.zero_add, Nat.sub_self, Nat.zero_div, fact,
    Nat.one_mul]
  congr <;> omega

theorem zero_leg_triSq_physical (b c p : Nat) (hp : p ≤ min b c) :
    triSq c b (zeroLegD b c p) =
      Q'.mkN (zeroLegDen b c p) (fact (zeroLegT b c p + 1) - 1) := by
  have hp' := Nat.le_min.mp hp
  have h1 : (c + b - zeroLegD b c p) / 2 = p := by
    unfold zeroLegD
    omega
  have h2 : (c + zeroLegD b c p - b) / 2 = c - p := by
    unfold zeroLegD
    omega
  have h3 : (b + zeroLegD b c p - c) / 2 = b - p := by
    unfold zeroLegD
    omega
  have h4 : (c + b + zeroLegD b c p) / 2 + 1 = zeroLegT b c p + 1 := by
    unfold zeroLegD zeroLegT
    omega
  unfold triSq triSqNum triSqDen
  rw [h1, h2, h3, h4]
  unfold zeroLegDen
  congr 1
  ac_rfl

theorem zero_leg_triSq_physical_swap (b c p : Nat) (hp : p ≤ min b c) :
    triSq c (zeroLegD b c p) b =
      Q'.mkN (zeroLegDen b c p) (fact (zeroLegT b c p + 1) - 1) := by
  have hp' := Nat.le_min.mp hp
  have h1 : (c + zeroLegD b c p - b) / 2 = c - p := by
    unfold zeroLegD
    omega
  have h2 : (c + b - zeroLegD b c p) / 2 = p := by
    unfold zeroLegD
    omega
  have h3 : (zeroLegD b c p + b - c) / 2 = b - p := by
    unfold zeroLegD
    omega
  have h4 : (c + zeroLegD b c p + b) / 2 + 1 = zeroLegT b c p + 1 := by
    unfold zeroLegD zeroLegT
    omega
  unfold triSq triSqNum triSqDen
  rw [h1, h2, h3, h4]
  unfold zeroLegDen
  exact rfl

private theorem zero_leg_factorial_product_cancel (b c p : Nat)
    (_hp : p ≤ min b c) :
    Q'.ofNat (b + 1) * Q'.ofNat (zeroLegD b c p + 1) *
      (Q'.mkN (fact b) (fact (b + 1) - 1) *
        Q'.mkN (fact (zeroLegD b c p))
          (fact (zeroLegD b c p + 1) - 1) *
        Q'.mkN (zeroLegDen b c p) (fact (zeroLegT b c p + 1) - 1) *
        Q'.mkN (zeroLegDen b c p) (fact (zeroLegT b c p + 1) - 1)) *
      (zeroLegRacahAmplitude b c p * zeroLegRacahAmplitude b c p) ≈ 1 := by
  have hDb : 0 < fact (b + 1) := fact_pos _
  have hDd : 0 < fact (zeroLegD b c p + 1) := fact_pos _
  have hT : 0 < fact (zeroLegT b c p + 1) := fact_pos _
  have hA : 0 < zeroLegDen b c p := by
    unfold zeroLegDen
    exact Nat.mul_pos (Nat.mul_pos (fact_pos _) (fact_pos _)) (fact_pos _)
  unfold zeroLegRacahAmplitude
  show _ * ((1 : Q').den : Int) = (1 : Q').num * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Int.mul_one, Int.one_mul]
  rw [mkN_den_of_pred _ _ hDb, mkN_den_of_pred _ _ hDd,
    mkN_den_of_pred _ _ hT, signed_den_of_pred _ _ hA]
  simp only [Q'.mkN, fact]
  by_cases hpar : zeroLegT b c p % 2 = 0
  · rw [if_pos hpar]
    push_cast
    simp only [Int.one_mul, Int.ofNat_eq_natCast, Int.natCast_mul,
      Int.natCast_add, Int.natCast_one]
    ac_rfl
  · rw [if_neg hpar]
    push_cast
    simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.one_mul,
      Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add, Int.natCast_one]
    ac_rfl

/-- **Symbolic zero-first-leg unit kernel.** -/
theorem zero_leg_racahKernel_eq_one (b c p : Nat)
    (hp : p ≤ min b c) :
    racahKernel6 0 b c (zeroLegD b c p) b (zeroLegD b c p) ≈ 1 := by
  unfold racahKernel6
  rw [if_pos (zero_leg_valid6 b c p hp)]
  have hsum := zero_leg_racahSum_eq_amplitude b c p hp
  have hprod :
      racahSum 0 b b c (zeroLegD b c p) (zeroLegD b c p) *
          racahSum 0 b b c (zeroLegD b c p) (zeroLegD b c p) ≈
        zeroLegRacahAmplitude b c p * zeroLegRacahAmplitude b c p := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hsum)
      (Q'.mul_eqv_congr_left _ _ _ hsum)
  rw [show dimRep b = b + 1 by rfl,
    show dimRep (zeroLegD b c p) = zeroLegD b c p + 1 by rfl,
    zero_leg_triSq_zero b, zero_leg_triSq_zero (zeroLegD b c p),
    zero_leg_triSq_physical b c p hp,
    zero_leg_triSq_physical_swap b c p hp]
  refine Q'.eqv_trans _
    (Q'.ofNat (b + 1) * Q'.ofNat (zeroLegD b c p + 1) *
      (Q'.mkN (fact b) (fact (b + 1) - 1) *
        Q'.mkN (fact (zeroLegD b c p))
          (fact (zeroLegD b c p + 1) - 1) *
        Q'.mkN (zeroLegDen b c p) (fact (zeroLegT b c p + 1) - 1) *
        Q'.mkN (zeroLegDen b c p) (fact (zeroLegT b c p + 1) - 1)) *
      (zeroLegRacahAmplitude b c p * zeroLegRacahAmplitude b c p)) _ ?_
    (zero_leg_factorial_product_cancel b c p hp)
  exact Q'.mul_eqv_congr_left _ _ _ hprod

/-! ## Closing the zero-leg squared target -/

theorem zero_family_collapsedRacahSquare (b c p : Nat)
    (hp : p ≤ min b c) :
    CollapsedRacahSquareAt (zeroLeftFamily b c p hp)
      (zeroRightFamily b c p hp) := by
  unfold CollapsedRacahSquareAt
  have he := (zero_family_intermediates b c p hp).1
  have hf := (zero_family_intermediates b c p hp).2
  rw [he, hf]
  change
    collapsedFactorialCrossSum (zeroLeftFamily b c p hp)
          (zeroRightFamily b c p hp) *
        collapsedFactorialCrossSum (zeroLeftFamily b c p hp)
          (zeroRightFamily b c p hp) ≈
      triLeftChannelWeight 0 b c (b + c - 2 * p) b *
        (triRightChannelWeight 0 b c (b + c - 2 * p) (b + c - 2 * p) *
          racahKernel6 0 b c (zeroLegD b c p) b (zeroLegD b c p))
  let W := Q'.ofNat (b + c - 2 * p + 1) * binaryRowFactorialProduct b c p
  have hC := zero_family_collapsedCross_closed b c p hp
  have hL := (zero_family_closed_factorial_normalization b c p hp).2.1
  have hR := (zero_family_closed_factorial_normalization b c p hp).2.2
  have hP := zero_leg_racahKernel_eq_one b c p hp
  have hleft :
      collapsedFactorialCrossSum (zeroLeftFamily b c p hp)
          (zeroRightFamily b c p hp) *
        collapsedFactorialCrossSum (zeroLeftFamily b c p hp)
          (zeroRightFamily b c p hp) ≈ W * W := by
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hC)
      (Q'.mul_eqv_congr_left _ _ _ hC)
  refine Q'.eqv_trans _ _ _ hleft ?_
  refine Q'.eqv_trans _ (W * (W * 1)) _
    (Q'.eqv_symm (Q'.mul_eqv_congr_left W _ _ (Q'.mul_one_eqv W))) ?_
  have hinner : W * 1 ≈
      triRightChannelWeight 0 b c (b + c - 2 * p) (b + c - 2 * p) *
        racahKernel6 0 b c (zeroLegD b c p) b (zeroLegD b c p) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hR))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hP))
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right W _ _ (Q'.eqv_symm hL))
    (Q'.mul_eqv_congr_left _ _ _ hinner)

end YMGap.Continuum.SU2OrderedRacahZeroLegKernel

#print axioms YMGap.Continuum.SU2OrderedRacahZeroLegKernel.zero_leg_valid6
#print axioms YMGap.Continuum.SU2OrderedRacahZeroLegKernel.zero_leg_racahSummand_onehot
#print axioms YMGap.Continuum.SU2OrderedRacahZeroLegKernel.zero_leg_racahSum_eq_amplitude
#print axioms YMGap.Continuum.SU2OrderedRacahZeroLegKernel.zero_leg_triSq_physical
#print axioms YMGap.Continuum.SU2OrderedRacahZeroLegKernel.zero_leg_triSq_physical_swap
#print axioms YMGap.Continuum.SU2OrderedRacahZeroLegKernel.zero_leg_racahKernel_eq_one
#print axioms YMGap.Continuum.SU2OrderedRacahZeroLegKernel.zero_family_collapsedRacahSquare
