/-
# Odd half of the response Jensen chain on the all-nome completed Wilson carrier

The one-step pairing `(y,z) ↦ B(y, T(1) z)` is a positive semidefinite form:
it is the plain completed pairing of the completed square roots,
`B(y, T(1) z) = B(S y, S z)` (`BF4WilsonAllNomeSquareRoot.squareRoot_pairing`).
Cauchy–Schwarz for it is therefore P1's completed Cauchy–Schwarz applied to the
square roots; no new form, carrier or time operator is built.

With the twisted Cauchy–Schwarz the odd lags become log-convex,
`R(m+n+1)^2 <= R(2m+1) R(2n+1)`, and together with P1's even log-convexity every
consecutive triple is log-convex, `R(k+1)^2 <= R(k) R(k+2)`, for
`R(k) = B(x, T(k) x)`. The generic ratio-floor engine of the even half
(`BF4WilsonAllNomeEvenResponseJensen.rc_logconvex_ratio_floor`) then runs on the
FULL integer chain, so a one-step floor `rho R(0) <= R(1)` gives the odd Jensen
bound `rho^n R(0) <= R(n)` (the constructive cleared form of
`R(n) R(0)^(n-1) >= R(1)^n`: zero cases need no case split) and the monotone
ratio floor `rho R(n) <= R(n+1)` at every lag, odd lags included.

Compiler: from the ONE-STEP relative energy `L * (R(0)-R(1)) <= delta * R(0)` and
a block split `s = L*k` we get the macro ratio `(1-delta)^k R(s) <= R(2s)` at any
lag `s` (no two-step conversion). The smoothed-state instance turns P3's open
`SmoothedCoherentEpsBound M scale c0` with `side scale = L*k`, `c0 <= k*delta`
into `SmoothedMacroRatio M scale ((1-delta)^k)`; `delta = 1/2`, `k = 2 c0`
gives `4^(-c0)`, and `(1 - c0/k)^k` tends to `e^(-c0)` as `k` grows. Constants
are rational powers; no exponential is used.

Non-degrading floor: the smoothed norm dominates the unsmoothed response at lag
`2M`, `R_x(2M) <= B(Y_M, Y_M)`, unconditionally. Hence the OPEN Prop
`FamilyRadiusSurvival M theta` (survival of the unsmoothed family over `2M`
steps) gives the smoothed floor `theta * varianceFloor * sum c^2`, with no
`(M+1)^(-2)` loss. Nothing here proves that Prop for side-uniform `theta`; from
a one-step floor it holds with `theta = rho^(2M)`, which degrades unless
`1 - rho = O(1/M)`.
-/

import YMGap.Continuum.BF4WilsonAllNomeEvenResponseJensen
import YMGap.Continuum.BF4WilsonAllNomeSquareRoot
import YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState

namespace YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity (varianceFloor)
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (Completion completedInner completedInner_nonnegative completedInner_symm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (completedTime completedTime_zero completedTime_add completedInner_time_sum
   completedInner_time_balance completedInner_oneStep_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeSquareRoot (squareRoot squareRoot_pairing)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime (responseSum)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (mixedMoment_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail (mixedMoment_time_decreasing)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyVariance
  (familyExcitation familyExcitation_norm_floor)
open YMGap.Continuum.BF4WilsonAllNomeCompletedLogConvexity (response_log_convex)
open YMGap.Continuum.BF4WilsonAllNomeEvenResponseJensen
  (rc_scale_chain rc_logconvex_ratio_floor rc_logconvex_geometric)
open YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState
  (smoothingWeight smoothingWeight_nonneg boxKernel timeKernel kernelMass timeKernel_mass
   smoothedCoherentVector smoothedResponse smoothedEnergy smoothedResponse_zero
   smoothedResponse_orbit_expand SmoothedMacroRatio SmoothedCoherentEpsBound)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)
local infix:50 " ≈ " => Q'.eqv

/-! ## Scalar helpers (local copies of the standard private lemmas) -/

private theorem od_ofNat_pos (L : Nat) (hL : 0 < L) : (0 : Q') < Q'.ofNat L := by
  change (0 : Int)*1 < (L : Int)*1
  simp only [Int.mul_one]
  omega

private theorem od_one_le_ofNat (L : Nat) (hL : 0 < L) : (1 : Q') ≤ Q'.ofNat L := by
  change (1 : Int)*1 ≤ (L : Int)*1
  simp only [Int.mul_one]
  omega

private theorem od_ofNat_mul (a b : Nat) :
    Q'.ofNat (a*b) ≈ Q'.ofNat a * Q'.ofNat b := by
  have hd1 : ((Q'.ofNat a * Q'.ofNat b).den : Int) = 1 := rfl
  have hd2 : ((Q'.ofNat (a*b)).den : Int) = 1 := rfl
  show ((a*b : Nat) : Int) * ((Q'.ofNat a * Q'.ofNat b).den : Int)
    = (((a : Nat) : Int) * ((b : Nat) : Int)) * ((Q'.ofNat (a*b)).den : Int)
  rw [hd1, hd2]
  push_cast
  omega

private theorem od_qpow_eqv_pow (y : Q') : ∀ n, (RGTransport.qpow y n).eqv (y^n)
  | 0 => Q'.eqv_refl _
  | n+1 => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ y (od_qpow_eqv_pow y n))
      (Q'.mul_comm_eqv _ _)

private theorem od_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _)
      (Q'.eqv_of_eq (Q'.zero_add' (A.approx n)))))

private theorem od_scale_coeff_add (a b : Q') (x : RC) :
    RCscale (a + b) x = RCadd (RCscale a x) (RCscale b x) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_mul_eqv a b (X.approx n)))

private theorem od_scale_rational (c q : Q') : RCscale c (Rq q) = Rq (c*q) := by
  rw [RCscale_mk]
  exact Quotient.sound (CRealAlg.ofQ'_mul c q).symm

private theorem od_response_lower (r : Q') (norm response : RC)
    (h : RCle (RCsub norm response) (RCscale r norm)) :
    RCle (RCscale (1-r) norm) response := by
  revert h
  refine Quotient.inductionOn₂ norm response ?_
  intro N F h epsilon he
  obtain ⟨index, hN⟩ := h epsilon he
  refine ⟨index, fun k hk => ?_⟩
  have hneg := Q'.add_le_add_left (N.approx k) _ _ (Q'.neg_le_neg_add (hN k hk))
  change (1-r)*N.approx k ≤ F.approx k + epsilon
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))
      (.add (.var 1) (.neg (.mul (.var 0) (.var 1)))) (by decide)
      (fun | 0 => r | _ => N.approx k)))
    (Q'.le_trans' _ _ _ hneg (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.add (.var 0) (.add (.neg (.add (.var 0) (.neg (.var 1)))) (.var 2)))
        (.add (.var 1) (.var 2)) (by decide)
        (fun | 0 => N.approx k | 1 => F.approx k | _ => epsilon))))

/-- Cancel a strictly positive rational scale on both sides. -/
private theorem od_scale_cancel {k : Q'} (hk : (0 : Q') < k) {a b : RC}
    (h : RCle (RCscale k a) (RCscale k b)) : RCle a b := by
  have h' := RCscale_mono (Q'.le_of_lt (Q'.recipPos_pos k hk)) h
  rw [RCscale_RCscale, RCscale_RCscale] at h'
  have e : Q'.recipPos k hk * k ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv k hk)
  rw [RCSignedPairBudget.scale_congr e, RCSignedPairBudget.scale_congr e,
    RCscale_one, RCscale_one] at h'
  exact h'

/-- `1 - delta <= 1 - a` from `a <= delta`. -/
private theorem od_one_sub_le {a delta : Q'} (h : a ≤ delta) :
    (1 : Q') - delta ≤ (1 : Q') - a :=
  Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg h)

/-! ## Box sums dominate constant lower bounds (mass times the bound) -/

theorem boxSum_ge_const {r : Q'} (hr : (0 : Q') ≤ r) (f : Nat → RC) (a : RC) :
    ∀ M : Nat, (∀ n, n ≤ M → RCle a (f n)) →
      RCle (RCscale (kernelMass (boxKernel r M)) a) (responseSum (boxKernel r M) f)
  | 0, h => by
      change RCle (RCscale (r + 0) a) (RCadd (RCscale r (f 0)) RCzero)
      rw [od_add_zero, RCSignedPairBudget.scale_congr
        (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv r 0) (Q'.eqv_of_eq (Q'.zero_add' r))) a]
      exact RCscale_mono hr (h 0 (Nat.le_refl 0))
  | m+1, h => by
      change RCle (RCscale (r + kernelMass (boxKernel r m)) a)
        (RCadd (RCscale r (f (m+1))) (responseSum (boxKernel r m) f))
      rw [od_scale_coeff_add]
      exact RCadd_le_add (RCscale_mono hr (h (m+1) (Nat.le_refl _)))
        (boxSum_ge_const hr f a m (fun n hn => h n (by omega)))

/-! ## Twisted Cauchy–Schwarz and full log-convexity -/

section Completed

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- PSD of the one-step pairing (re-export of the time-defect positivity). -/
theorem oneStep_form_nonnegative (y : V) : RCnonneg (B y (T 1 y)) :=
  completedInner_oneStep_nonnegative hw0 hw1 y

/-- Symmetry of the one-step pairing (time balance plus symmetry). -/
theorem oneStep_symmetric (y z : V) : B y (T 1 z) = B z (T 1 y) := by
  rw [← completedInner_time_balance hw0 hw1 1 y z, completedInner_symm hw0 hw1]

/-- Cauchy–Schwarz for the one-step pairing `B(y, T(1) z)`, via the completed
square root: it is P1's Cauchy–Schwarz for `(S y, S z)`. -/
theorem oneStep_cauchySchwarz (y z : V) :
    RCle (RCmul (B y (T 1 z)) (B y (T 1 z)))
      (RCmul (B y (T 1 y)) (B z (T 1 z))) := by
  have h := BF4WilsonAllNomeCompletedLogConvexity.completedInner_cauchySchwarz hw0 hw1 width
    (squareRoot hw0 hw1 y) (squareRoot hw0 hw1 z)
  rw [squareRoot_pairing hw0 hw1 y z, squareRoot_pairing hw0 hw1 y y,
    squareRoot_pairing hw0 hw1 z z] at h
  exact h

/-- Every response `R(k) = B(x, T(k) x)` is nonnegative. -/
theorem response_nonnegative (x : V) (k : Nat) : RCnonneg (B x (T k x)) :=
  mixedMoment_nonnegative hw0 hw1 x k 0

/-- Odd-lag log-convexity `R(m+n+1)^2 <= R(2m+1) R(2n+1)`. -/
theorem response_odd_log_convex (x : V) (m n : Nat) :
    RCle (RCmul (B x (T (m+n+1) x)) (B x (T (m+n+1) x)))
      (RCmul (B x (T (2*m+1) x)) (B x (T (2*n+1) x))) := by
  have h := oneStep_cauchySchwarz hw0 hw1 width (T m x) (T n x)
  have e : ∀ a b : Nat, B (T a x) (T 1 (T b x)) = B x (T (a+b+1) x) := by
    intro a b
    rw [← completedTime_add hw0 hw1 1 b x, completedInner_time_sum hw0 hw1 a (1+b) x x,
      show a + (1+b) = a+b+1 by omega]
  rw [e m n, e m m, e n n, show m+m+1 = 2*m+1 by omega,
    show n+n+1 = 2*n+1 by omega] at h
  exact h

/-- Log-convexity of EVERY consecutive triple `R(k+1)^2 <= R(k) R(k+2)`:
even `k` from P1's even log-convexity, odd `k` from the twisted one. -/
theorem response_log_convex_step (x : V) (k : Nat) :
    RCle (RCmul (B x (T (k+1) x)) (B x (T (k+1) x)))
      (RCmul (B x (T k x)) (B x (T (k+2) x))) := by
  obtain ⟨j, hj | hj⟩ : ∃ j, k = 2*j ∨ k = 2*j+1 := ⟨k/2, by omega⟩
  · have h := response_log_convex hw0 hw1 width x j (j+1)
    rw [show j+(j+1) = k+1 by omega, show 2*(j+1) = k+2 by omega,
      show 2*j = k by omega] at h
    exact h
  · have h := response_odd_log_convex hw0 hw1 width x j (j+1)
    rw [show j+(j+1)+1 = k+1 by omega, show 2*(j+1)+1 = k+2 by omega,
      show 2*j+1 = k by omega] at h
    exact h

/-- Responses are antitone in the lag (additive form). -/
theorem response_antitone (x : V) (a : Nat) :
    ∀ d : Nat, RCle (B x (T (a+d) x)) (B x (T a x))
  | 0 => RCle_refl _
  | d+1 => RCle_trans (mixedMoment_time_decreasing hw0 hw1 x (a+d) 0)
      (response_antitone x a d)

theorem response_le_of_le (x : V) {a b : Nat} (h : a ≤ b) :
    RCle (B x (T b x)) (B x (T a x)) := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  exact response_antitone hw0 hw1 width x a d

/-! ## The odd (one-step) Jensen chain -/

/-- Monotone ratio floor at EVERY lag: `rho R(n) <= R(n+1)` from the one-step
floor `rho R(0) <= R(1)` and a rational norm floor. -/
theorem response_ratio_floor (x : V) (rho q : Q') (hrho : (0 : Q') < rho)
    (hq : (0 : Q') < q) (hnorm : RCle (Rq q) (B x x))
    (h1 : RCle (RCscale rho (B x x)) (B x (T 1 x))) :
    ∀ n : Nat, RCle (RCscale rho (B x (T n x))) (B x (T (n+1) x)) := by
  let E : Nat → RC := fun k => B x (T k x)
  have e0 : E 0 = B x x := by
    show B x (T 0 x) = B x x
    rw [completedTime_zero hw0 hw1]
  have h0 : RCle (RCscale 1 (Rq q)) (E 0) := by
    rw [RCscale_one, e0]
    exact hnorm
  have h1' : RCle (RCscale rho (E 0)) (E 1) := by
    rw [e0]
    exact h1
  intro n
  exact (rc_logconvex_ratio_floor E rho q hrho hq h0
    (fun k => response_nonnegative hw0 hw1 width x k)
    (fun k => response_log_convex_step hw0 hw1 width x k) h1' n).1

/-- Odd Jensen bound, cleared constructive form of `R(n) R(0)^(n-1) >= R(1)^n`:
`rho^n R(0) <= R(n)` for every `n` from `rho R(0) <= R(1)`. -/
theorem response_odd_jensen (x : V) (rho q : Q') (hrho : (0 : Q') < rho)
    (hq : (0 : Q') < q) (hnorm : RCle (Rq q) (B x x))
    (h1 : RCle (RCscale rho (B x x)) (B x (T 1 x))) :
    ∀ n : Nat, RCle (RCscale (rho^n) (B x x)) (B x (T n x)) := by
  let E : Nat → RC := fun k => B x (T k x)
  have e0 : E 0 = B x x := by
    show B x (T 0 x) = B x x
    rw [completedTime_zero hw0 hw1]
  have h0 : RCle (RCscale 1 (Rq q)) (E 0) := by
    rw [RCscale_one, e0]
    exact hnorm
  have h1' : RCle (RCscale rho (E 0)) (E 1) := by
    rw [e0]
    exact h1
  intro n
  have h := rc_logconvex_geometric E rho q hrho hq h0
    (fun k => response_nonnegative hw0 hw1 width x k)
    (fun k => response_log_convex_step hw0 hw1 width x k) h1' n
  rw [e0] at h
  exact h

/-- Shifted chain `rho^j R(n) <= R(n+j)`. -/
theorem response_shift_floor (x : V) (rho q : Q') (hrho : (0 : Q') < rho)
    (hq : (0 : Q') < q) (hnorm : RCle (Rq q) (B x x))
    (h1 : RCle (RCscale rho (B x x)) (B x (T 1 x))) (n : Nat) :
    ∀ j : Nat, RCle (RCscale (rho^j) (B x (T n x))) (B x (T (n+j) x))
  | 0 => by
      show RCle (RCscale 1 (B x (T n x))) (B x (T (n+0) x))
      rw [RCscale_one]
      exact RCle_refl _
  | j+1 => rc_scale_chain _ _ _ (rho^j) rho (Q'.le_of_lt hrho)
      (response_shift_floor x rho q hrho hq hnorm h1 n j)
      (response_ratio_floor hw0 hw1 width x rho q hrho hq hnorm h1 (n+j))

/-- Macro ratio at ANY lag `s` (odd included) from the one-step floor:
`rho^s R(s) <= R(2s)`. -/
theorem macro_ratio_of_oneStep_floor (x : V) (s : Nat) (rho q : Q')
    (hrho : (0 : Q') < rho) (hq : (0 : Q') < q) (hnorm : RCle (Rq q) (B x x))
    (h1 : RCle (RCscale rho (B x x)) (B x (T 1 x))) :
    RCle (RCscale (rho^s) (B x (T s x))) (B x (T (s+s) x)) :=
  response_shift_floor hw0 hw1 width x rho q hrho hq hnorm h1 s s

/-- Block compiler off the odd chain with a general Bernoulli constant:
`s = L*k`, `L t <= delta < 1`, one-step floor `(1-t) R(0) <= R(1)` give
`(1-delta)^k R(s) <= R(2s)`. -/
theorem macro_ratio_of_oneStep_block (x : V) (s L k : Nat) (hs : s = L*k)
    (t delta q : Q') (ht0 : (0 : Q') ≤ t) (ht1 : t < (1 : Q')) (hdelta : delta < (1 : Q'))
    (hq : (0 : Q') < q) (hLt : Q'.ofNat L * t ≤ delta)
    (hnorm : RCle (Rq q) (B x x))
    (h1 : RCle (RCscale ((1 : Q') - t) (B x x)) (B x (T 1 x))) :
    RCle (RCscale (((1 : Q') - delta)^k) (B x (T s x))) (B x (T (s+s) x)) := by
  have hrho : (0 : Q') < (1 : Q') - t := HKPos.one_sub_pos ht1
  have hbern := BondMovingRetuneFix.bernoulli_oneSub t ht0 (Q'.le_of_lt ht1) L
  have hblock : (1 : Q') - delta ≤ ((1 : Q') - t)^L :=
    Q'.le_trans' _ _ _ (od_one_sub_le hLt)
      (Q'.le_trans' _ _ _ hbern (Q'.le_of_eqv (od_qpow_eqv_pow _ L)))
  have hd0 : (0 : Q') ≤ (1 : Q') - delta := Q'.le_of_lt (HKPos.one_sub_pos hdelta)
  have hpow : ((1 : Q') - delta)^k ≤ ((1 : Q') - t)^s := by
    rw [hs]
    exact Q'.le_trans' _ _ _
      (CRealLog.pow_le_pow_base _ _ hd0 hblock k)
      (Q'.le_of_eqv (FiveHolonomyPerronCutoff.pow_mul_eqv _ L k))
  exact RCle_trans (RCscale_scalar_mono hpow (response_nonnegative hw0 hw1 width x s))
    (macro_ratio_of_oneStep_floor hw0 hw1 width x s ((1 : Q') - t) q hrho hq hnorm h1)

/-- Energy form: `L * (R(0) - R(1)) <= delta * R(0)` with `L > 0`,
`0 <= delta < 1` and `s = L*k` give `(1-delta)^k R(s) <= R(2s)`. -/
theorem macro_ratio_of_oneStep_block_energy (x : V) (s L k : Nat) (hs : s = L*k)
    (hL : 0 < L) (delta q : Q') (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hq : (0 : Q') < q) (hnorm : RCle (Rq q) (B x x))
    (hE : RCle (RCscale (Q'.ofNat L) (RCsub (B x x) (B x (T 1 x))))
      (RCscale delta (B x x))) :
    RCle (RCscale (((1 : Q') - delta)^k) (B x (T s x))) (B x (T (s+s) x)) := by
  have hLpos := od_ofNat_pos L hL
  let r : Q' := Q'.recipPos (Q'.ofNat L) hLpos
  have hr0 : (0 : Q') ≤ r := Q'.le_of_lt (Q'.recipPos_pos _ _)
  have hLr : Q'.ofNat L * r ≈ 1 := Q'.mul_recipPos_eqv _ _
  have hr1 : r ≤ 1 :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv r))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ r (od_one_le_ofNat L hL) hr0)
        (Q'.le_of_eqv hLr))
  have ht0 : (0 : Q') ≤ delta * r := Q'.mul_nonneg _ _ hdelta0 hr0
  have htd : delta * r ≤ delta :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ delta hr1 hdelta0)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.one_mul_eqv delta)))
  have ht1 : delta * r < (1 : Q') := HKPos.q_lt_of_le_of_lt htd hdelta
  have hLt : Q'.ofNat L * (delta * r) ≤ delta := by
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _ ?_
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ delta hLr) (Q'.one_mul_eqv delta)))
    exact poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => Q'.ofNat L | 1 => delta | _ => r)
  have hEr := RCscale_mono hr0 hE
  rw [RCscale_RCscale, RCscale_RCscale] at hEr
  have hrL : r * Q'.ofNat L ≈ 1 := Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) hLr
  rw [RCSignedPairBudget.scale_congr hrL, RCscale_one,
    RCSignedPairBudget.scale_congr (Q'.mul_comm_eqv r delta)] at hEr
  exact macro_ratio_of_oneStep_block hw0 hw1 width x s L k hs (delta * r) delta q ht0 ht1
    hdelta hq hLt hnorm (od_response_lower (delta * r) _ _ hEr)

end Completed

/-! ## Smoothed coherent state: odd compiler and the non-degrading floor -/

section Smoothed

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
  (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width)

local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "x0" => Subtype.val (familyExcitation hw0 hw1 width qs c hqs)
local notation "Y" M:arg => smoothedCoherentVector hw0 hw1 width qs c hqs M

/-- Odd-chain compiler for P3's open eps-bound: `side scale = L*k`, `k > 0`,
`c0 <= k*delta`, `0 <= delta < 1` give the macro ratio `(1-delta)^k`. With
`delta = 1/2`, `k = 2 c0` this is `4^(-c0)`. -/
theorem smoothed_macroRatio_of_epsBound_odd (hn : qs.Nodup)
    (hc : (0 : Q') < listQSum (fun face => c face*c face) qs) (M scale L k : Nat)
    (hs : side scale = L*k) (hk : 0 < k) (c0 delta : Q')
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hc0 : c0 ≤ Q'.ofNat k * delta)
    (heps : SmoothedCoherentEpsBound hw0 hw1 width qs c hqs M scale c0) :
    SmoothedMacroRatio hw0 hw1 width qs c hqs M scale (((1 : Q') - delta)^k) := by
  have hL : 0 < L := by
    refine Nat.pos_of_ne_zero (fun h0 => ?_)
    have hside := BF4DyadicWilsonSquare.side_positive scale
    rw [hs, h0, Nat.zero_mul] at hside
    exact absurd hside (Nat.lt_irrefl 0)
  have hkpos := od_ofNat_pos k hk
  have hN := completedInner_nonnegative hw0 hw1 (Y M)
  have hside : Q'.ofNat (side scale) ≈ Q'.ofNat k * Q'.ofNat L := by
    rw [hs]
    exact Q'.eqv_trans _ _ _ (od_ofNat_mul L k) (Q'.mul_comm_eqv _ _)
  have h1 : RCle (RCscale (Q'.ofNat k)
        (RCscale (Q'.ofNat L) (smoothedEnergy hw0 hw1 width qs c hqs M)))
      (RCscale (Q'.ofNat k) (RCscale delta (B (Y M) (Y M)))) := by
    rw [RCscale_RCscale, RCscale_RCscale, ← RCSignedPairBudget.scale_congr hside]
    exact RCle_trans heps (RCscale_scalar_mono hc0 hN)
  have hE := od_scale_cancel hkpos h1
  have hnorm := BF4WilsonAllNomeSmoothedCoherentState.smoothedCoherent_norm_floor
    hw0 hw1 width qs c hqs hn M
  have h := macro_ratio_of_oneStep_block_energy hw0 hw1 width (Y M) (side scale) L k hs hL
    delta _ hdelta0 hdelta
    (BF4WilsonAllNomeSmoothedCoherentState.smoothedNormFloor_positive hw0 hw1 qs c hc M)
    hnorm hE
  unfold SmoothedMacroRatio smoothedResponse
  rw [show 2 * side scale = side scale + side scale by omega]
  exact h

/-- Unconditional: the smoothed norm dominates the UNSMOOTHED response at lag
`2M` (unit kernel mass, antitone responses); no `(M+1)^(-2)` loss. -/
theorem smoothedCoherent_norm_ge_family_response (M : Nat) :
    RCle (B x0 (T (2*M) x0)) (B (Y M) (Y M)) := by
  have hr := smoothingWeight_nonneg M
  rw [← smoothedResponse_zero hw0 hw1 width qs c hqs M,
    smoothedResponse_orbit_expand hw0 hw1 width qs c hqs M 0]
  have hinner : ∀ m, m ≤ M →
      RCle (RCscale (kernelMass (timeKernel M)) (B x0 (T (2*M) x0)))
        (responseSum (timeKernel M) (fun k => B x0 (T (m+k+0) x0))) := fun m hm =>
    boxSum_ge_const hr (fun k => B x0 (T (m+k+0) x0)) _ M
      (fun k hk => response_le_of_le hw0 hw1 width x0 (by omega : m+k+0 ≤ 2*M))
  have houter : RCle (RCscale (kernelMass (timeKernel M))
        (RCscale (kernelMass (timeKernel M)) (B x0 (T (2*M) x0))))
      (responseSum (timeKernel M)
        (fun m => responseSum (timeKernel M) (fun k => B x0 (T (m+k+0) x0)))) :=
    boxSum_ge_const hr _ _ M hinner
  have hm := timeKernel_mass M
  have hmm : kernelMass (timeKernel M) * kernelMass (timeKernel M) ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hm)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hm) (Q'.one_mul_eqv 1))
  rw [RCscale_RCscale, RCSignedPairBudget.scale_congr hmm, RCscale_one] at houter
  exact houter

/-- OPEN (not proved here): survival of the UNSMOOTHED coherent family over
`2M` steps, `theta * B(x,x) <= B(x, T(2M) x)`. A side-uniform `theta` for
`M ~ side` is a genuinely new input of the same difficulty as raw survival. -/
def FamilyRadiusSurvival (M : Nat) (theta : Q') : Prop :=
  RCle (RCscale theta (B x0 x0)) (B x0 (T (2*M) x0))

/-- OPEN target (not proved here): the smoothed coherent state at radius `M`
has norm at least `v`. It is NON-DEGRADING when `v` is chosen independently of
`M` and `side scale`. -/
def SmoothedCoherentNonDegradingFloor (M : Nat) (v : Q') : Prop :=
  RCle (Rq v) (B (Y M) (Y M))

/-- Reduction: family survival over `2M` steps gives the non-degrading smoothed
floor `theta * varianceFloor * sum c^2` (distinct faces). -/
theorem smoothedFloor_of_familyRadiusSurvival (hn : qs.Nodup) (M : Nat) (theta : Q')
    (htheta : (0 : Q') ≤ theta)
    (hsurv : FamilyRadiusSurvival hw0 hw1 width qs c hqs M theta) :
    SmoothedCoherentNonDegradingFloor hw0 hw1 width qs c hqs M
      (theta * (varianceFloor w hw0 * listQSum (fun face => c face*c face) qs)) := by
  have hf := familyExcitation_norm_floor hw0 hw1 width qs c hqs hn
  have h := RCscale_mono htheta hf
  rw [od_scale_rational] at h
  exact RCle_trans h (RCle_trans hsurv
    (smoothedCoherent_norm_ge_family_response hw0 hw1 width qs c hqs M))

/-- What IS provable from the odd chain: a one-step floor on the unsmoothed
family gives `FamilyRadiusSurvival M (rho^(2M))` (degrading unless
`1 - rho = O(1/M)`). -/
theorem familyRadiusSurvival_of_oneStep_floor (hn : qs.Nodup) (M : Nat) (rho : Q')
    (hrho : (0 : Q') < rho)
    (hc : (0 : Q') < listQSum (fun face => c face*c face) qs)
    (h1 : RCle (RCscale rho (B x0 x0)) (B x0 (T 1 x0))) :
    FamilyRadiusSurvival hw0 hw1 width qs c hqs M (rho^(2*M)) :=
  response_odd_jensen hw0 hw1 width x0 rho _ hrho
    (Q'.mul_pos (BF4ExactSlabPlaquetteAffineCoercivity.varianceFloor_positive hw0 hw1) hc)
    (familyExcitation_norm_floor hw0 hw1 width qs c hqs hn) h1 (2*M)

end Smoothed

#print axioms boxSum_ge_const
#print axioms oneStep_form_nonnegative
#print axioms oneStep_symmetric
#print axioms oneStep_cauchySchwarz
#print axioms response_nonnegative
#print axioms response_odd_log_convex
#print axioms response_log_convex_step
#print axioms response_antitone
#print axioms response_le_of_le
#print axioms response_ratio_floor
#print axioms response_odd_jensen
#print axioms response_shift_floor
#print axioms macro_ratio_of_oneStep_floor
#print axioms macro_ratio_of_oneStep_block
#print axioms macro_ratio_of_oneStep_block_energy
#print axioms smoothed_macroRatio_of_epsBound_odd
#print axioms smoothedCoherent_norm_ge_family_response
#print axioms smoothedFloor_of_familyRadiusSurvival
#print axioms familyRadiusSurvival_of_oneStep_floor

end YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen
