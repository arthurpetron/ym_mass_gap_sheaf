/-
# Constructive relaxed form rate on the completed centered SU(2) carrier

The quotient module already proves a squared finite-Haar cross-form estimate
for the centered product heat map.  This module records the strongest next
finite statement that does not require choosing a square root in `Q'`: with
`r = (1 + q) / 2`, where `q = squaredHeatRate w`, the cross form is bounded
by `r` times the finite Haar norm up to an arbitrary positive rational slack.
The slack form is the one that can be lifted directly through the constructive
`CReal` order.

This is a finite ordinary-Haar SU(2) carrier estimate.  It is not an
Osterwalder--Schrader identification, a physical spectral gap, or a
thermodynamic/continuum result.
-/

import YMGap.Constructive.Sqrt
import YMGap.Constructive.ExpNeg
import YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient

namespace YMGap.Continuum.SU2QuaternionFiniteHaarMidpointFormRate

set_option autoImplicit false
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier
open YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionRelativeHeatContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast_local : (0 : Q').num = 0 := rfl
private theorem zero_den_cast_local : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast_local : (1 : Q').num = 1 := rfl
private theorem one_den_cast_local : ((1 : Q').den : Int) = 1 := rfl
private theorem two_num_cast_local : (2 : Q').num = 2 := rfl
private theorem two_den_cast_local : ((2 : Q').den : Int) = 1 := rfl

private theorem sq_add_local (u v : Q') :
    ((u + v) * (u + v)).eqv ((u * u + u * v) + (u * v + v * v)) := by
  refine Q'.eqv_trans _ _ _ (QPoly.q_add_mul u v (u + v)) ?_
  refine QPoly.q_add_congr (Q'.mul_add_eqv u u v) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv v u v) ?_
  exact QPoly.q_add_congr (Q'.mul_comm_eqv v u) (Q'.eqv_refl (v * v))

private theorem sq_sub_local (u v : Q') :
    ((u + -v) * (u + -v)).eqv
      ((u * u + -(u * v)) + (-(u * v) + v * v)) := by
  refine Q'.eqv_trans _ _ _ (sq_add_local u (-v)) ?_
  refine QPoly.q_add_congr ?_ ?_
  · exact QPoly.q_add_congr (Q'.eqv_refl (u * u)) (Q'.mul_neg_eqv u v)
  · refine QPoly.q_add_congr (Q'.mul_neg_eqv u v) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv v (-v)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv v v)) ?_
    exact Q'.neg_neg_eqv (v * v)

private theorem sq_add_reordered_local (u v : Q') :
    ((u + v) * (u + v)).eqv ((u * u + v * v) + (u * v + u * v)) := by
  refine Q'.eqv_trans _ _ _ (sq_add_local u v) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (u * u + u * v) (u * v + v * v) (v * v + u * v)
      (Q'.add_comm_eqv (u * v) (v * v))) ?_
  exact Q'.add_swap_inner (u * u) (u * v) (v * v) (u * v)

private theorem sq_sub_reordered_local (u v : Q') :
    ((u + -v) * (u + -v)).eqv
      ((u * u + v * v) + -(u * v + u * v)) := by
  refine Q'.eqv_trans _ _ _ (sq_sub_local u v) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (u * u + -(u * v)) (-(u * v) + v * v)
      (v * v + -(u * v)) (Q'.add_comm_eqv (-(u * v)) (v * v))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_swap_inner (u * u) (-(u * v)) (v * v) (-(u * v))) ?_
  exact Q'.add_eqv_congr_left (u * u + v * v) (-(u * v) + -(u * v))
    (-(u * v + u * v)) (Q'.eqv_symm (Q'.neg_add_eqv (u * v) (u * v)))

private theorem sub_add_cancel_local (a b : Q') :
    a.eqv ((a + (-b)) + b) := by
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left a ((-b) + b) 0 (Q'.neg_add_self_eqv b)) ?_
  exact QPoly.q_add_zero_eqv a

private theorem midpoint_square_identity_local (q : Q') :
    q +
        (Q'.mkPos 1 2 (by decide) * ((1 : Q') + -q)) *
          (Q'.mkPos 1 2 (by decide) * ((1 : Q') + -q)) ≈
      (Q'.mkPos 1 2 (by decide) * ((1 : Q') + q)) *
        (Q'.mkPos 1 2 (by decide) * ((1 : Q') + q)) := by
  let h : Q' := Q'.mkPos 1 2 (by decide)
  let b : Q' := h * q
  let c : Q' := h * b + h * b
  let d : Q' := h * h + b * b
  have hplus : h * ((1 : Q') + q) ≈ h + b := by
    dsimp [b]
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv h 1 q) ?_
    exact QPoly.q_add_congr (Q'.mul_one_eqv h) (Q'.eqv_refl (h * q))
  have hminus : h * ((1 : Q') + -q) ≈ h + -b := by
    dsimp [b]
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv h 1 (-q)) ?_
    exact QPoly.q_add_congr (Q'.mul_one_eqv h) (Q'.mul_neg_eqv h q)
  have hplusSq :
      (h * ((1 : Q') + q)) * (h * ((1 : Q') + q)) ≈ d + c := by
    dsimp [b, c, d]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hplus) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (h + h * q) _ _ hplus) ?_
    exact sq_add_reordered_local h (h * q)
  have hminusSq :
      (h * ((1 : Q') + -q)) * (h * ((1 : Q') + -q)) ≈ d + -c := by
    dsimp [b, c, d]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hminus) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (h + -(h * q)) _ _ hminus) ?_
    exact sq_sub_reordered_local h (h * q)
  have hhalf : (h + h).eqv (1 : Q') := by
    exact ExpNeg.half_add_half_eqv
  have hc : c ≈ h * q := by
    dsimp [c, b]
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (QPoly.q_add_mul h h (h * q))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (h + h) 1 (h * q) hhalf) ?_
    exact Q'.one_mul_eqv (h * q)
  have hqcc : q ≈ c + c := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (ExpNeg.two_halves q)) ?_
    exact QPoly.q_add_congr (Q'.eqv_symm hc) (Q'.eqv_symm hc)
  have hcancel : c + -c ≈ (0 : Q') := by
    refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv c (-c)) ?_
    exact Q'.neg_add_self_eqv c
  have hcore : q + (d + -c) ≈ d + c := by
    refine Q'.eqv_trans _ _ _
      (QPoly.q_add_congr hqcc (Q'.eqv_refl (d + -c))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_swap_inner c c d (-c)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (c + d) (c + -c) 0 hcancel) ?_
    refine Q'.eqv_trans _ _ _ (QPoly.q_add_zero_eqv (c + d)) ?_
    exact Q'.add_comm_eqv c d
  refine Q'.eqv_trans _ _ _
    (QPoly.q_add_congr (Q'.eqv_refl q) hminusSq) ?_
  refine Q'.eqv_trans _ _ _ hcore (Q'.eqv_symm hplusSq)

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast_local, zero_den_cast_local,
               one_num_cast_local, one_den_cast_local,
               two_num_cast_local, two_den_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add,
               Int.add_assoc, Int.mul_assoc, Int.add_comm, Int.mul_comm,
               Int.add_left_comm, Int.mul_left_comm,
               Int.two_mul, Int.reduceMul, Int.reduceAdd];
             try ac_rfl))

/-- The rational relaxed rate `r = (1+q)/2`. -/
def midpointRate (q : Q') : Q' :=
  Q'.mkPos 1 2 (by decide) * ((1 : Q') + q)

private theorem midpointRate_nonnegative {q : Q'}
    (hq : (0 : Q') ≤ q) :
    (0 : Q') ≤ midpointRate q := by
  unfold midpointRate
  exact Q'.mul_nonneg _ _ (by decide)
    (Q'.zero_le_add _ _ (by decide) hq)

private theorem midpointRate_positive {q : Q'}
    (hq : (0 : Q') ≤ q) :
    (0 : Q') < midpointRate q := by
  unfold midpointRate
  exact Q'.mul_pos (by decide)
    (Q'.pos_add_nonneg (by decide) hq)

private theorem midpointRate_sq_ge {q : Q'}
    (hq1 : q ≤ (1 : Q')) :
    q ≤ midpointRate q * midpointRate q := by
  let d : Q' := (1 : Q') + -q
  have hd : (0 : Q') ≤ d := by
    dsimp [d]
    exact Q'.sub_nonneg_of_le hq1
  have hdsq : (0 : Q') ≤
      (Q'.mkPos 1 2 (by decide) * d) *
        (Q'.mkPos 1 2 (by decide) * d) :=
    SumOfSquares.q_mul_self_nonneg _
  have hadd : q ≤ q +
      (Q'.mkPos 1 2 (by decide) * d) *
        (Q'.mkPos 1 2 (by decide) * d) :=
    Q'.add_le_self_of_nonneg _ _ hdsq
  have hid : q +
      (Q'.mkPos 1 2 (by decide) * d) *
        (Q'.mkPos 1 2 (by decide) * d) ≈
      midpointRate q * midpointRate q := by
    change q +
        (Q'.mkPos 1 2 (by decide) * ((1 : Q') + -q)) *
          (Q'.mkPos 1 2 (by decide) * ((1 : Q') + -q)) ≈
      (Q'.mkPos 1 2 (by decide) * ((1 : Q') + q)) *
        (Q'.mkPos 1 2 (by decide) * ((1 : Q') + q))
    exact midpoint_square_identity_local q
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hid)

/--
For every positive rational slack, the centered finite cross form is bounded
by the relaxed midpoint rate times the finite Haar norm plus that slack.

The slack formulation is intentional: it is exactly the constructive order
interface needed for a `CReal` limit, and it avoids a nonconstructive square
root choice at the rational representative level.
-/
theorem productMapQuotient_transfer_form_midpoint_le_add
    (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hnodup : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n)
    (p : (finiteHaarGNSData n).V)
    (hcenter : quaternionHaar n p.val ≈ 0)
    (ε : Q') (hε : (0 : Q') < ε) :
    kineticPair n w K ids p.val p.val ≤
      midpointRate (squaredHeatRate w) * finiteHaarPair n p.val p.val + ε := by
  let c : Q' := kineticPair n w K ids p.val p.val
  let N : Q' := finiteHaarPair n p.val p.val
  let r : Q' := midpointRate (squaredHeatRate w)
  have hc : (0 : Q') ≤ c := by
    dsimp [c]
    exact kineticPair_nonnegative n w (Q'.le_of_lt hw0) K ids hids
      p.val p.property
  have hN : (0 : Q') ≤ N := by
    dsimp [N]
    exact finiteHaarPair_nonnegative n p.val p.property
  have hq : (0 : Q') ≤ squaredHeatRate w :=
    squaredHeatRate_nonnegative hw0 hw1
  have hq1 : squaredHeatRate w ≤ (1 : Q') :=
    Q'.le_of_lt (squaredHeatRate_lt_one hw0 hw1)
  have hr0 : (0 : Q') ≤ r := by
    dsimp [r]
    exact midpointRate_nonnegative hq
  have hrr : squaredHeatRate w ≤ r * r := by
    dsimp [r]
    exact midpointRate_sq_ge hq1
  have hNN : (0 : Q') ≤ N * N :=
    SumOfSquares.q_mul_self_nonneg N
  have hscaled : squaredHeatRate w * (N * N) ≤
      (r * r) * (N * N) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hrr hNN
  have hsq : c * c ≤ squaredHeatRate w * (N * N) := by
    dsimp [c, N]
    exact productMapQuotient_transfer_form_squared_bound n hw0 hw1 K hK ids
      hnodup hids p hcenter
  have hbase : c * c ≤ (r * N) * (r * N) := by
    have hrrN : (r * r) * (N * N) ≈ (r * N) * (r * N) := by
      q_ring
    exact Q'.le_trans' _ _ _ hsq
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hrrN))
  have hRN : (0 : Q') ≤ r * N :=
    Q'.mul_nonneg _ _ hr0 hN
  have hsqSlack : (r * N) * (r * N) ≤
      (ε + r * N) * (ε + r * N) := by
    have hexpand : (ε + r * N) * (ε + r * N) ≈
        (ε * ε + (r * N) * (r * N)) +
          (ε * (r * N) + ε * (r * N)) := by
      exact CReal.sq_add_expand ε (r * N)
    have hεsq : (0 : Q') ≤ ε * ε :=
      SumOfSquares.q_mul_self_nonneg ε
    have hcross : (0 : Q') ≤ ε * (r * N) + ε * (r * N) :=
      Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (Q'.le_of_lt hε) hRN)
        (Q'.mul_nonneg _ _ (Q'.le_of_lt hε) hRN)
    have hbase' : (r * N) * (r * N) ≤
        ε * ε + (r * N) * (r * N) := by
      have hzero : (r * N) * (r * N) ≤
          (r * N) * (r * N) + ε * ε := by
        exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (Q'.eqv_symm (QPoly.q_add_zero_eqv ((r * N) * (r * N)))))
          (Q'.add_le_add_left ((r * N) * (r * N)) 0 (ε * ε) hεsq)
      exact Q'.le_trans' _ _ _ hzero
        (Q'.le_of_eqv (Q'.add_comm_eqv
          ((r * N) * (r * N)) (ε * ε)))
    exact Q'.le_trans' _ _ _
      hbase'
      (Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg _ _ hcross)
        (Q'.ge_of_eqv hexpand))
  have htarget : c * c ≤ (ε + r * N) * (ε + r * N) :=
    Q'.le_trans' _ _ _ hbase hsqSlack
  have hupper : c ≤ ε + r * N :=
    CReal.le_of_sq_le_sq (Q'.pos_add_nonneg hε hRN) hc htarget
  dsimp [c, N, r] at hupper ⊢
  exact Q'.le_trans' _ _ _ hupper
    (Q'.le_of_eqv (Q'.add_comm_eqv ε
      (midpointRate (squaredHeatRate w) * finiteHaarPair n p.val p.val)))

#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarMidpointFormRate.midpointRate
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarMidpointFormRate.midpointRate_sq_ge
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarMidpointFormRate.productMapQuotient_transfer_form_midpoint_le_add

end YMGap.Continuum.SU2QuaternionFiniteHaarMidpointFormRate
