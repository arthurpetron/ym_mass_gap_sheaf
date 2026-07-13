/-
# Pascal midpoint square for the cleared theta residual

Under the Bernstein substitution `w=t/(1+t)`, a monomial `w^e` at degree
`D` becomes `M(D,e)=t^e(1+t)^(D-e)`.  The integer exponents neighboring the
half-integer exponent are exactly symmetric:

  e, e+a, e+2a,   a=2n+1.

This module proves the generic weighted midpoint factorization

  n^2 M_e + (n+1)^2 M_(e+2a) - 2n(n+1) M_(e+a)
    = t^e(1+t)^(D-e-2a)
        [n(1+t)^a-(n+1)t^a]^2.

It is the coefficient-positive square atom in any Pascal/Gosper telescope
for the full cleared theta residual.
-/

import YMGap.Continuum.ThetaResidualBernsteinPilot
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.ThetaResidualPascalTelescope

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-- Degree-`D` Bernstein transform of the monomial `w^e`. -/
def bernMon (D e : Nat) (t : Q') : Q' :=
  qpow t e * qpow ((1 : Q') + t) (D - e)

private theorem mul_eqv_both {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

private theorem pow_two_eqv (x : Q') : qpow x 2 ≈ x * x := by
  change ((1 : Q') * x) * x ≈ x * x
  exact Q'.mul_eqv_congr_right _ _ x (Q'.one_mul_eqv x)

private theorem pow_add_twice (x : Q') (b a : Nat) :
    qpow x (b + (a + a)) ≈ qpow x b * (qpow x a * qpow x a) := by
  refine Q'.eqv_trans _ _ _ (qpow_add x b (a + a)) ?_
  exact Q'.mul_eqv_congr_left (qpow x b) _ _ (qpow_add x a a)

/-- Left endpoint extraction `M_e = common*(1+t)^a^2`. -/
theorem bernMon_left_extract {D e a : Nat} (h : e + (a + a) ≤ D) (t : Q') :
    bernMon D e t ≈
      (qpow t e * qpow (1 + t) (D - (e + (a + a)))) *
        (qpow (1 + t) a * qpow (1 + t) a) := by
  unfold bernMon
  have hd : D - e = (D - (e + (a + a))) + (a + a) := by omega
  rw [hd]
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (qpow t e) _ _
      (pow_add_twice (1 + t) (D - (e + (a + a))) a)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

/-- Right endpoint extraction `M_(e+2a) = common*t^a^2`. -/
theorem bernMon_right_extract {D e a : Nat} (h : e + (a + a) ≤ D) (t : Q') :
    bernMon D (e + (a + a)) t ≈
      (qpow t e * qpow (1 + t) (D - (e + (a + a)))) *
        (qpow t a * qpow t a) := by
  unfold bernMon
  have ht : qpow t (e + (a + a)) ≈
      qpow t e * (qpow t a * qpow t a) := pow_add_twice t e a
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ht) ?_
  -- `(te*(ta*ta))*u = (te*u)*(ta*ta)`.
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

/-- Midpoint extraction `M_(e+a) = common*(1+t)^a*t^a`. -/
theorem bernMon_mid_extract {D e a : Nat} (h : e + (a + a) ≤ D) (t : Q') :
    bernMon D (e + a) t ≈
      (qpow t e * qpow (1 + t) (D - (e + (a + a)))) *
        (qpow (1 + t) a * qpow t a) := by
  unfold bernMon
  have hd : D - (e + a) = (D - (e + (a + a))) + a := by omega
  rw [hd]
  have ht := qpow_add t e a
  have hu := qpow_add (1 + t) (D - (e + (a + a))) a
  refine Q'.eqv_trans _ _ _ (mul_eqv_both ht hu) ?_
  -- `(te*ta)*(u*ua) = (te*u)*(ua*ta)`.
  have hrearr :
      (qpow t e * qpow t a) *
          (qpow (1 + t) (D - (e + (a + a))) * qpow (1 + t) a) ≈
        (qpow t e * qpow (1 + t) (D - (e + (a + a)))) *
          (qpow (1 + t) a * qpow t a) := by
    ring_qeqv
  exact hrearr

/-- **Generic Pascal weighted-midpoint square.** -/
theorem bernMon_weighted_midpoint_square {D e a n : Nat}
    (h : e + (a + a) ≤ D) (t : Q') :
    (Q'.ofNat n * Q'.ofNat n) * bernMon D e t +
        (Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) *
          bernMon D (e + (a + a)) t +
        (-(Q'.ofNat 2 *
          ((Q'.ofNat n * Q'.ofNat (n + 1)) * bernMon D (e + a) t))) ≈
      (qpow t e * qpow (1 + t) (D - (e + (a + a)))) *
        ((Q'.ofNat n * qpow (1 + t) a +
            -(Q'.ofNat (n + 1) * qpow t a)) *
          (Q'.ofNat n * qpow (1 + t) a +
            -(Q'.ofNat (n + 1) * qpow t a))) := by
  let C := qpow t e * qpow (1 + t) (D - (e + (a + a)))
  let X := qpow (1 + t) a
  let Y := qpow t a
  have hL := bernMon_left_extract h t
  have hR := bernMon_right_extract h t
  have hM := bernMon_mid_extract h t
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ hL)
        (Q'.mul_eqv_congr_left _ _ _ hR))
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
          (Q'.mul_eqv_congr_left _ _ _ hM)))) ?_
  change
    (Q'.ofNat n * Q'.ofNat n) * (C * (X * X)) +
        (Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) * (C * (Y * Y)) +
        (-(Q'.ofNat 2 *
          ((Q'.ofNat n * Q'.ofNat (n + 1)) * (C * (X * Y))))) ≈
      C * ((Q'.ofNat n * X + -(Q'.ofNat (n + 1) * Y)) *
        (Q'.ofNat n * X + -(Q'.ofNat (n + 1) * Y)))
  have hs := ThetaResidualBernsteinPilot.weighted_midpoint_square n X Y
  -- Pull the common factor `C` through the three summands.
  have hrearr :
      (Q'.ofNat n * Q'.ofNat n) * (C * (X * X)) +
          (Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) * (C * (Y * Y)) +
          (-(Q'.ofNat 2 *
            ((Q'.ofNat n * Q'.ofNat (n + 1)) * (C * (X * Y))))) ≈
        C * (((Q'.ofNat n * Q'.ofNat n) * (X * X) +
          (Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) * (Y * Y)) +
          (-(Q'.ofNat 2 *
            ((Q'.ofNat n * Q'.ofNat (n + 1)) * (X * Y))))) := by
    ring_qeqv
  exact Q'.eqv_trans _ _ _ hrearr
    (Q'.mul_eqv_congr_left C _ _ hs)

/-- The square atom is nonnegative for `t>=0`. -/
theorem bernMon_weighted_midpoint_nonneg {D e a n : Nat}
    (h : e + (a + a) ≤ D) {t : Q'} (ht : (0 : Q') ≤ t) :
    (0 : Q') ≤
      (Q'.ofNat n * Q'.ofNat n) * bernMon D e t +
        (Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) *
          bernMon D (e + (a + a)) t +
        (-(Q'.ofNat 2 *
          ((Q'.ofNat n * Q'.ofNat (n + 1)) * bernMon D (e + a) t))) := by
  let C := qpow t e * qpow (1 + t) (D - (e + (a + a)))
  let Z := Q'.ofNat n * qpow (1 + t) a +
    -(Q'.ofNat (n + 1) * qpow t a)
  have h1t : (0 : Q') ≤ (1 : Q') + t := Q'.zero_le_add _ _ (by decide) ht
  have hC : (0 : Q') ≤ C := Q'.mul_nonneg _ _
    (qpow_nonneg t ht e) (qpow_nonneg (1 + t) h1t _)
  have hsq : (0 : Q') ≤ Z * Z := SumOfSquares.q_mul_self_nonneg Z
  exact Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ hC hsq)
    (Q'.le_of_eqv (Q'.eqv_symm (bernMon_weighted_midpoint_square h t)))

/-! ## Obstruction to a one-monomial Gosper reserve

The endpoint values at `t=1` suggest the reserve

  R_j = 4 j(j-1) M(D, 2j(j-1)-1).

This puts `R_j` at the preceding half-edge exponent.  It cannot work:
at local cell `n=2`, Bernstein coefficient `k=3`, the physical diagonal and
off-diagonal terms have not started yet, but `R_2` contributes `8`.  Thus
`diag_2-off_2-R_2+R_3` has coefficient exactly `-8`, for every degree `D>=3`.
-/

private def monoCoeff (D e k : Nat) : Int :=
  if e ≤ k then Int.ofNat (PNPaths.choose (D - e) (k - e)) else 0

private def diagCoeff (D n k : Nat) : Int :=
  Int.ofNat (n * n) *
    (monoCoeff D (2 * n * n - 2) k +
      3 * monoCoeff D (2 * n * n - 1) k +
      3 * monoCoeff D (2 * n * n) k +
      monoCoeff D (2 * n * n + 1) k)

private def offCoeff (D n k : Nat) : Int :=
  Int.ofNat (8 * n * (n + 1)) *
    monoCoeff D (2 * n * (n + 1) - 1) k

/-- Coefficient of the natural preceding-edge monomial reserve. -/
private def prevEdgeReserveCoeff (D j k : Nat) : Int :=
  if j = 0 then 0 else
    Int.ofNat (4 * j * (j - 1)) *
      monoCoeff D (2 * j * (j - 1) - 1) k

private def prevEdgeLocalCoeff (D n k : Nat) : Int :=
  diagCoeff D n k - offCoeff D n k - prevEdgeReserveCoeff D n k +
    prevEdgeReserveCoeff D (n + 1) k

/-- **Uniform kernel refutation.**  The preceding-half-edge one-monomial
Gosper family fails at the same coefficient for every cutoff degree. -/
theorem prevEdge_one_monomial_obstructed (D : Nat) :
    prevEdgeLocalCoeff D 2 3 = (-8 : Int) := by
  simp [prevEdgeLocalCoeff, diagCoeff, offCoeff, prevEdgeReserveCoeff,
    monoCoeff, PNPaths.choose]

/-- Consequently that local remainder is not coefficientwise nonnegative. -/
theorem prevEdge_one_monomial_not_nonnegative (D : Nat) :
    ¬ ((0 : Int) ≤ prevEdgeLocalCoeff D 2 3) := by
  rw [prevEdge_one_monomial_obstructed D]
  decide

/-! ## Obstruction to the first two-monomial shift

Moving the preceding-edge reserve one or two Pascal steps to the right does
not repair the problem, even if the two weights are allowed to vary with the
cutoff.  Write

  R_j = 4 j(j-1) (p M(D,2j(j-1)) + q M(D,2j(j-1)+1)).

At cell `n=2` the physical diagonal starts only at exponent six.  The
coefficient at four therefore sees just `-8p`.  If that coefficient is
nonnegative then `p=0`; the coefficient at five then sees just `-8q`.
Thus no nonzero pair of nonnegative weights can make even these two
coefficients nonnegative.  This is uniform in `D` and does not assume a
normalization such as `p+q=1`.
-/

private def shiftedTwoReserveCoeff (D p q j k : Nat) : Int :=
  if j = 0 then 0 else
    Int.ofNat (4 * j * (j - 1)) *
      ((p : Int) * monoCoeff D (2 * j * (j - 1)) k +
        (q : Int) * monoCoeff D (2 * j * (j - 1) + 1) k)

private def shiftedTwoLocalCoeff (D p q n k : Nat) : Int :=
  diagCoeff D n k - offCoeff D n k - shiftedTwoReserveCoeff D p q n k +
    shiftedTwoReserveCoeff D p q (n + 1) k

/-- The first exposed coefficient of the shifted two-monomial reserve. -/
theorem shiftedTwo_local_four (D p q : Nat) :
    shiftedTwoLocalCoeff D p q 2 4 = -(8 * (p : Int)) := by
  simp [shiftedTwoLocalCoeff, shiftedTwoReserveCoeff, diagCoeff, offCoeff,
    monoCoeff, PNPaths.choose]

/-- Once the first weight vanishes, the next coefficient exposes the second
weight, independently of the cutoff degree. -/
theorem shiftedTwo_local_five_of_first_zero (D q : Nat) :
    shiftedTwoLocalCoeff D 0 q 2 5 = -(8 * (q : Int)) := by
  simp [shiftedTwoLocalCoeff, shiftedTwoReserveCoeff, diagCoeff, offCoeff,
    monoCoeff, PNPaths.choose]

/-- **Uniform two-cell obstruction.**  No nonzero nonnegative pair of
weights in the first two shifted Pascal monomials gives a coefficientwise
nonnegative local remainder. -/
theorem shiftedTwo_nonnegative_obstructed (D p q : Nat) (hpq : 0 < p + q) :
    ¬ ((0 : Int) ≤ shiftedTwoLocalCoeff D p q 2 4 ∧
      (0 : Int) ≤ shiftedTwoLocalCoeff D p q 2 5) := by
  intro h
  have hp : p = 0 := by
    rw [shiftedTwo_local_four D p q] at h
    omega
  subst p
  rw [shiftedTwo_local_five_of_first_zero D q] at h
  omega

/-! Allowing cancellation between signed monomial weights does not open a
loophole.  If the flux itself is required to have nonnegative Bernstein
coefficients, its coefficients at four and five, together with those of the
local remainder, force both weights to vanish.  At cutoff two the unreserved
local coefficient at twenty-two is then `-80`. -/

private def signedShiftedTwoReserveCoeff (D j k : Nat) (p q : Int) : Int :=
  if j = 0 then 0 else
    Int.ofNat (4 * j * (j - 1)) *
      (p * monoCoeff D (2 * j * (j - 1)) k +
        q * monoCoeff D (2 * j * (j - 1) + 1) k)

private def signedShiftedTwoLocalCoeff (D n k : Nat) (p q : Int) : Int :=
  diagCoeff D n k - offCoeff D n k -
      signedShiftedTwoReserveCoeff D n k p q +
    signedShiftedTwoReserveCoeff D (n + 1) k p q

private theorem signed_reserve_two_four (p q : Int) :
    signedShiftedTwoReserveCoeff 23 2 4 p q = 8 * p := by
  simp [signedShiftedTwoReserveCoeff, monoCoeff, PNPaths.choose]

private theorem signed_local_two_four (p q : Int) :
    signedShiftedTwoLocalCoeff 23 2 4 p q = -(8 * p) := by
  simp [signedShiftedTwoLocalCoeff, signedShiftedTwoReserveCoeff, diagCoeff,
    offCoeff, monoCoeff, PNPaths.choose]

private theorem signed_reserve_two_five_of_first_zero (q : Int) :
    signedShiftedTwoReserveCoeff 23 2 5 0 q = 8 * q := by
  simp [signedShiftedTwoReserveCoeff, monoCoeff, PNPaths.choose]

private theorem signed_local_two_five_of_first_zero (q : Int) :
    signedShiftedTwoLocalCoeff 23 2 5 0 q = -(8 * q) := by
  simp [signedShiftedTwoLocalCoeff, signedShiftedTwoReserveCoeff, diagCoeff,
    offCoeff, monoCoeff, PNPaths.choose]

private theorem signed_local_two_top_zero :
    signedShiftedTwoLocalCoeff 23 2 22 0 0 = (-80 : Int) := by decide

/-- **Signed-family obstruction at the first nontrivial cutoff.**  No signed
two-term shift can simultaneously keep the reserve and the local remainder
coefficientwise nonnegative. -/
theorem shiftedTwo_signed_cutoff_two_obstructed (p q : Int) :
    ¬ ((0 : Int) ≤ signedShiftedTwoReserveCoeff 23 2 4 p q ∧
      (0 : Int) ≤ signedShiftedTwoLocalCoeff 23 2 4 p q ∧
      (0 : Int) ≤ signedShiftedTwoReserveCoeff 23 2 5 p q ∧
      (0 : Int) ≤ signedShiftedTwoLocalCoeff 23 2 5 p q ∧
      (0 : Int) ≤ signedShiftedTwoLocalCoeff 23 2 22 p q) := by
  intro h
  have hp : p = 0 := by
    rw [signed_reserve_two_four p q] at h
    rw [signed_local_two_four p q] at h
    omega
  subst p
  have hq : q = 0 := by
    rw [signed_reserve_two_five_of_first_zero q] at h
    rw [signed_local_two_five_of_first_zero q] at h
    omega
  subst q
  rw [signed_local_two_top_zero] at h
  omega

/-! ## Reverse-cumulative multi-cell flux at the top coefficient

The failed fixed-shape reserves motivate using the actual reverse cumulative
coefficient as the flux.  The top Bernstein coefficient is the first place
where this multi-cell mechanism has a closed form: every transformed
monomial contributes one.  A tail with `c` off-diagonal cells, beginning at
cell `n`, therefore has value

  4 (2 n (n+c) + c(c+1)).

The formula is strictly cutoff-uniform and exposes the exact recurrence: the
new left cell changes the reverse flux by `-8n`, while the positive terminal
diagonal supplies the boundary value. -/

private theorem choose_zero_of_lt : ∀ n k : Nat, n < k → PNPaths.choose n k = 0
  | _, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
      simp only [PNPaths.choose]
      rw [choose_zero_of_lt n k (by omega)]
      rw [choose_zero_of_lt n (k + 1) (by omega)]

private theorem choose_self : ∀ n : Nat, PNPaths.choose n n = 1
  | 0 => rfl
  | n + 1 => by
      simp only [PNPaths.choose]
      rw [choose_self n]
      rw [choose_zero_of_lt n (n + 1) (by omega)]

/-- Raising the top entry of a binomial coefficient preserves order. -/
theorem choose_top_add_mono (T d r : Nat) :
    PNPaths.choose T r ≤ PNPaths.choose (T+d) r := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hadd : T+(d+1)=(T+d)+1 := by omega
      rw [hadd]
      cases r with
      | zero => simp [PNPaths.choose]
      | succ r =>
          simp only [PNPaths.choose]
          omega

/-- First-order Pascal accumulation: after `d` degree elevations, the
starting coefficient and `d` copies of its left neighbor are present. -/
theorem choose_top_add_linear (T d q : Nat) :
    PNPaths.choose T (q+1)+d*PNPaths.choose T q ≤
      PNPaths.choose (T+d) (q+1) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hadd : T+(d+1)=(T+d)+1 := by omega
      rw [hadd]
      simp only [PNPaths.choose]
      have hm := choose_top_add_mono T d q
      simp only [Nat.add_mul]
      omega

private theorem monoCoeff_top {D e : Nat} (h : e ≤ D) :
    monoCoeff D e D = 1 := by
  simp [monoCoeff, h, choose_self]

private theorem diagCoeff_top {D n : Nat} (h : 2 * n * n + 1 ≤ D) :
    diagCoeff D n D = Int.ofNat (n * n) * 8 := by
  have h0 : 2 * n * n - 2 ≤ D := by omega
  have h1 : 2 * n * n - 1 ≤ D := by omega
  have h2 : 2 * n * n ≤ D := by omega
  simp [diagCoeff, monoCoeff_top h0, monoCoeff_top h1,
    monoCoeff_top h2, monoCoeff_top h]

private theorem offCoeff_top {D n : Nat}
    (h : 2 * n * (n + 1) - 1 ≤ D) :
    offCoeff D n D = Int.ofNat (8 * n * (n + 1)) := by
  simp [offCoeff, monoCoeff_top h]

/-- Exact reverse-cumulative Bernstein coefficient: `c=0` is the terminal
diagonal, and each successor prepends one diagonal-minus-off cell. -/
def reverseTailCoeff (D n k : Nat) : Nat → Int
  | 0 => diagCoeff D n k
  | c + 1 =>
      diagCoeff D n k - offCoeff D n k +
        reverseTailCoeff D (n + 1) k c

/-- Closed nonnegative numerator of the top reverse flux. -/
def reverseTopFluxNat (n c : Nat) : Nat :=
  4 * (2 * n * (n + c) + c * (c + 1))

theorem reverseTopFluxNat_step (n c : Nat) :
    reverseTopFluxNat n (c + 1) + 8 * n =
      reverseTopFluxNat (n + 1) c := by
  simp only [reverseTopFluxNat, Nat.mul_add, Nat.add_mul]
  omega

private theorem top_cell_drift (n : Nat) :
    Int.ofNat (n * n) * 8 - Int.ofNat (8 * n * (n + 1)) =
      -(8 * Int.ofNat n) := by
  rw [Int.mul_comm 8 (Int.ofNat n)]
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add,
    Int.mul_add, Int.sub_eq_add_neg, Int.neg_add]
  have h8 : ((8 : Nat) : Int) = (8 : Int) := rfl
  rw [h8]
  have hsq : (n : Int) * (n : Int) * 8 = 8 * (n : Int) * (n : Int) := by
    ac_rfl
  have hlin : 8 * (n : Int) * ((1 : Nat) : Int) = (n : Int) * 8 := by
    change 8 * (n : Int) * 1 = (n : Int) * 8
    ac_rfl
  rw [hsq, hlin]
  omega

/-- The generic top-coefficient reverse flux is the stated positive natural
number.  This is an exact multi-cell recurrence for arbitrary start cell and
tail length, not a finite-cutoff computation. -/
theorem reverseTailCoeff_top (D n c : Nat)
    (hD : 2 * (n + c) * (n + c) + 1 ≤ D) :
    reverseTailCoeff D n D c = Int.ofNat (reverseTopFluxNat n c) := by
  induction c generalizing n with
  | zero =>
      simp only [Nat.add_zero] at hD
      rw [reverseTailCoeff]
      rw [diagCoeff_top (by simpa using hD)]
      simp [reverseTopFluxNat]
      rw [show (8 : Int) = 4 * 2 by decide]
      ac_rfl
  | succ c ih =>
      rw [reverseTailCoeff]
      have hnle : n ≤ n + (c + 1) := by omega
      have hn1le : n + 1 ≤ n + (c + 1) := by omega
      have hsquare : n * n ≤ (n + (c + 1)) * (n + (c + 1)) :=
        Nat.mul_le_mul hnle hnle
      have hrect : n * (n + 1) ≤ (n + (c + 1)) * (n + (c + 1)) :=
        Nat.mul_le_mul hnle hn1le
      have hn : 2 * n * n + 1 ≤ D := by
        simp only [Nat.mul_assoc] at hD ⊢
        omega
      have hoff : 2 * n * (n + 1) - 1 ≤ D := by
        simp only [Nat.mul_assoc] at hD ⊢
        omega
      rw [diagCoeff_top hn, offCoeff_top hoff]
      rw [top_cell_drift n]
      rw [ih (n + 1) (by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hD)]
      have hstep := reverseTopFluxNat_step n c
      have hstepI := congrArg Int.ofNat hstep
      simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul]
        at ⊢ hstepI
      omega

theorem reverseTailCoeff_top_nonnegative (D n c : Nat)
    (hD : 2 * (n + c) * (n + c) + 1 ≤ D) :
    (0 : Int) ≤ reverseTailCoeff D n D c := by
  rw [reverseTailCoeff_top D n c hD]
  exact Int.natCast_nonneg _

/-! ## Two-parameter Pascal descent

Degree elevation acts locally on every Bernstein monomial coefficient.  In
ordinary coefficient coordinates this is

  B(D+1,k+1) = B(D,k) + B(D,k+1).

For the deficit coordinate `r=D-k`, the same identity says that the
`(D+1,r+1)` reverse-tail flux is the sum of the `(D,r+1)` and `(D,r)`
fluxes.  Hence nonnegativity propagates monotonically through the entire
Pascal triangle once a lower-degree row is controlled. -/

private theorem monoCoeff_degree_step {D e k : Nat} (heD : e ≤ D) :
    monoCoeff (D + 1) e (k + 1) =
      monoCoeff D e k + monoCoeff D e (k + 1) := by
  by_cases hek : e ≤ k
  · have hek1 : e ≤ k + 1 := by omega
    have hDe : D + 1 - e = (D - e) + 1 := by omega
    have hke : k + 1 - e = (k - e) + 1 := by omega
    simp only [monoCoeff, if_pos hek, if_pos hek1]
    rw [hDe, hke, PNPaths.choose]
    simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  · by_cases hek1 : e ≤ k + 1
    · have heq : e = k + 1 := by omega
      subst e
      simp [monoCoeff, PNPaths.choose, hek]
    · simp [monoCoeff, hek, hek1]

private theorem diagCoeff_degree_step {D n k : Nat}
    (hD : 2 * n * n + 1 ≤ D) :
    diagCoeff (D + 1) n (k + 1) =
      diagCoeff D n k + diagCoeff D n (k + 1) := by
  have h0 : 2 * n * n - 2 ≤ D := by omega
  have h1 : 2 * n * n - 1 ≤ D := by omega
  have h2 : 2 * n * n ≤ D := by omega
  simp only [diagCoeff, monoCoeff_degree_step h0, monoCoeff_degree_step h1,
    monoCoeff_degree_step h2, monoCoeff_degree_step hD, Int.mul_add]
  ac_rfl

private theorem offCoeff_degree_step {D n k : Nat}
    (hD : 2 * n * (n + 1) - 1 ≤ D) :
    offCoeff (D + 1) n (k + 1) =
      offCoeff D n k + offCoeff D n (k + 1) := by
  simp only [offCoeff, monoCoeff_degree_step hD, Int.mul_add]

/-- **Generic two-parameter reverse-flux recurrence.**  Elevating the degree
by one replaces a reverse-tail coefficient by the sum of its two Pascal
parents. -/
theorem reverseTailCoeff_degree_step (D n k c : Nat)
    (hD : 2 * (n + c) * (n + c) + 1 ≤ D) :
    reverseTailCoeff (D + 1) n (k + 1) c =
      reverseTailCoeff D n k c + reverseTailCoeff D n (k + 1) c := by
  induction c generalizing n with
  | zero =>
      simp only [reverseTailCoeff]
      exact diagCoeff_degree_step (by simpa using hD)
  | succ c ih =>
      simp only [reverseTailCoeff]
      have hnle : n ≤ n + (c + 1) := by omega
      have hn1le : n + 1 ≤ n + (c + 1) := by omega
      have hsquare : n * n ≤ (n + (c + 1)) * (n + (c + 1)) :=
        Nat.mul_le_mul hnle hnle
      have hrect : n * (n + 1) ≤ (n + (c + 1)) * (n + (c + 1)) :=
        Nat.mul_le_mul hnle hn1le
      have hn : 2 * n * n + 1 ≤ D := by
        simp only [Nat.mul_assoc] at hD ⊢
        omega
      have hoff : 2 * n * (n + 1) - 1 ≤ D := by
        simp only [Nat.mul_assoc] at hD ⊢
        omega
      rw [diagCoeff_degree_step hn, offCoeff_degree_step hoff]
      rw [ih (n + 1) (by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hD)]
      simp only [Int.sub_eq_add_neg, Int.neg_add]
      ac_rfl

/-- Deficit-coordinate form of `reverseTailCoeff_degree_step`. -/
theorem reverseTailCoeff_deficit_step (D n c r : Nat) (hr : r < D)
    (hD : 2 * (n + c) * (n + c) + 1 ≤ D) :
    reverseTailCoeff (D + 1) n ((D + 1) - (r + 1)) c =
      reverseTailCoeff D n (D - (r + 1)) c +
        reverseTailCoeff D n (D - r) c := by
  have hk : D - (r + 1) + 1 = D - r := by omega
  have hk' : (D + 1) - (r + 1) = D - r := by omega
  simpa [hk, hk'] using
    (reverseTailCoeff_degree_step D n (D - (r + 1)) c hD)

/-- The deficit descent preserves nonnegativity. -/
theorem reverseTailCoeff_deficit_nonnegative (D n c r : Nat) (hr : r < D)
    (hD : 2 * (n + c) * (n + c) + 1 ≤ D)
    (hnext : (0 : Int) ≤ reverseTailCoeff D n (D - (r + 1)) c)
    (hcur : (0 : Int) ≤ reverseTailCoeff D n (D - r) c) :
    (0 : Int) ≤
      reverseTailCoeff (D + 1) n ((D + 1) - (r + 1)) c := by
  rw [reverseTailCoeff_deficit_step D n c r hr hD]
  omega

/-! ## The signed minimal-degree boundary band -/

private theorem choose_pred : ∀ n : Nat, PNPaths.choose (n + 1) n = n + 1
  | 0 => rfl
  | n + 1 => by
      simp only [PNPaths.choose]
      rw [choose_pred n, choose_self]
      rw [choose_zero_of_lt n (n + 1) (by omega)]

private theorem choose_zero : ∀ n : Nat, PNPaths.choose n 0=1
  | 0 => rfl
  | _+1 => rfl

private theorem choose_one : ∀ n : Nat, PNPaths.choose n 1=n
  | 0 => rfl
  | n+1 => by
      simp only [PNPaths.choose,choose_one n,choose_zero n]
      omega

/-- Adjacent-binomial cross identity, in a subtraction-free range form. -/
theorem choose_adjacent_cross : ∀ T q : Nat, q<T →
    (q+1)*PNPaths.choose T (q+1)=(T-q)*PNPaths.choose T q
  | 0, q, h => by omega
  | T+1, 0, _ => by rw [choose_one,choose_zero]; omega
  | T+1, q+1, h => by
      by_cases hlt : q+1<T
      · simp only [PNPaths.choose]
        have h1:=choose_adjacent_cross T q (by omega)
        have h2:=choose_adjacent_cross T (q+1) hlt
        have htop:T+1-(q+1)=T-q:=by omega
        rw [htop]
        have hs:T-q=(T-(q+1))+1:=by omega
        rw [hs] at h1 ⊢
        rw [Nat.mul_add,Nat.mul_add]
        rw [h2]
        have hqa : (q+1+1)*PNPaths.choose T (q+1) =
            (q+1)*PNPaths.choose T (q+1)+PNPaths.choose T (q+1) := by
          rw [Nat.add_mul]
          simp
        rw [hqa,h1]
        simp only [Nat.add_mul,Nat.one_mul]
        omega
      · have heq:q+1=T:=by omega
        subst T
        rw [choose_self,choose_pred (q+1)]
        have hs:q+1+1-(q+1)=1:=by omega
        rw [hs]
        omega

/-- The degree gap in the through-`b₃` induction doubles the smaller
off-diagonal binomial coefficient. -/
theorem choose_remainder_off_double (m r : Nat) (hm : 2≤m)
    (hr : 4≤r) (hrT : r≤2*m+4) :
    2*PNPaths.choose (2*m+4) r≤PNPaths.choose (4*m+2) r := by
  let T:=2*m+4
  let d:=2*m-2
  have hTd : T+d=4*m+2 := by dsimp [T,d]; omega
  have hrpos : 0<r := by omega
  have hrpred : r-1<T := by dsimp [T]; omega
  have hadj := choose_adjacent_cross T (r-1) hrpred
  have hrback : r-1+1=r := by omega
  have hTback : T-(r-1)=T-r+1 := by omega
  rw [hrback,hTback] at hadj
  have hcoef : T-r+1≤d*r := by
    have hfour : T-r+1≤4*d := by dsimp [T,d]; omega
    have hdr : 4*d≤r*d := Nat.mul_le_mul_right d hr
    have hcomm : d*r=r*d := by ac_rfl
    rw [hcomm]
    exact Nat.le_trans hfour hdr
  have hscaled : r*PNPaths.choose T r≤r*(d*PNPaths.choose T (r-1)) := by
    calc
      r*PNPaths.choose T r = (T-r+1)*PNPaths.choose T (r-1) := hadj
      _ ≤ (d*r)*PNPaths.choose T (r-1) := Nat.mul_le_mul_right _ hcoef
      _ = r*(d*PNPaths.choose T (r-1)) := by ac_rfl
  have hpay : PNPaths.choose T r≤d*PNPaths.choose T (r-1) :=
    Nat.le_of_mul_le_mul_left hscaled hrpos
  have hlin := choose_top_add_linear T d (r-1)
  rw [hrback,hTd] at hlin
  calc
    2*PNPaths.choose T r = PNPaths.choose T r+PNPaths.choose T r := by omega
    _ ≤ PNPaths.choose T r+d*PNPaths.choose T (r-1) :=
      Nat.add_le_add_left hpay _
    _ ≤ PNPaths.choose (4*m+2) r := hlin

private theorem monoCoeff_top_one {D e : Nat} (hDpos : 0 < D) (heD : e ≤ D) :
    monoCoeff D e (D - 1) = Int.ofNat (D - e) := by
  by_cases he : e < D
  · have hek : e ≤ D - 1 := by omega
    simp only [monoCoeff, if_pos hek]
    have harg : D - 1 - e = (D - e) - 1 := by omega
    rw [harg]
    cases hq : D - e with
    | zero => omega
    | succ q => simp only [Nat.add_sub_cancel, choose_pred]
  · have heq : e = D := by omega
    subst e
    simp [monoCoeff, show ¬ D ≤ D - 1 by omega]

private def topOneDiagNat (D n : Nat) : Nat :=
  n * n * (8 * D - 16 * n * n + 4)

private def topOneOffNat (D n : Nat) : Nat :=
  8 * n * (n + 1) * (D - (2 * n * (n + 1) - 1))

private theorem diagCoeff_top_one {D n : Nat} (hnpos : 0 < n)
    (hD : 2 * n * n + 1 ≤ D) :
    diagCoeff D n (D - 1) = Int.ofNat (topOneDiagNat D n) := by
  have h0 : 2 * n * n - 2 ≤ D := by omega
  have h1 : 2 * n * n - 1 ≤ D := by omega
  have h2 : 2 * n * n ≤ D := by omega
  have hDpos : 0 < D := by omega
  rw [diagCoeff]
  rw [monoCoeff_top_one hDpos h0, monoCoeff_top_one hDpos h1,
    monoCoeff_top_one hDpos h2, monoCoeff_top_one hDpos hD]
  have hsquare : 1 ≤ n * n := Nat.mul_le_mul hnpos hnpos
  have hsum :
      (D - (2 * n * n - 2)) + 3 * (D - (2 * n * n - 1)) +
          3 * (D - 2 * n * n) + (D - (2 * n * n + 1)) =
        8 * D - 16 * n * n + 4 := by
    simp only [Nat.mul_assoc] at hD ⊢
    omega
  have hcast := congrArg Int.ofNat hsum
  simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul] at hcast
  unfold topOneDiagNat
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add]
  have h3 : ((3 : Nat) : Int) = (3 : Int) := rfl
  rw [h3] at hcast
  exact congrArg (fun z : Int => (n : Int) * (n : Int) * z) hcast

private theorem offCoeff_top_one {D n : Nat}
    (hDpos : 0 < D) (hD : 2 * n * (n + 1) - 1 ≤ D) :
    offCoeff D n (D - 1) = Int.ofNat (topOneOffNat D n) := by
  rw [offCoeff, monoCoeff_top_one hDpos hD]
  simp [topOneOffNat, Int.natCast_mul]

private theorem top_one_algebra (x d : Int) :
    x * x * (8 * d - 16 * x * x + 4) -
        8 * x * (x + 1) * (d - (2 * x * (x + 1) - 1)) =
      0 - 8 * d * x + 32 * x * x * x + 12 * x * x - 8 * x := by
  simp only [Int.mul_add, Int.add_mul, Int.sub_eq_add_neg, Int.neg_add,
    Int.mul_neg, Int.mul_one]
  have h1 : x*x*(8*d) = 8*x*x*d := by ac_rfl
  have h2 : 8*x*d = 8*d*x := by ac_rfl
  have h3 : x*x*(16*x*x) = 16*x*x*x*x := by ac_rfl
  have h4 : 8*x*x*(2*x*x) = 16*x*x*x*x := by ac_rfl
  have h5 : 8*x*(2*x*x) = 16*x*x*x := by ac_rfl
  have h6 : 8*x*x*(2*x) = 16*x*x*x := by ac_rfl
  have h7 : 8*x*(2*x) = 16*x*x := by ac_rfl
  have h8 : 32*x*x*x = 2*(8*x*x*(2*x)) := by ac_rfl
  have h9 : 16*x*x = 16*(x*x) := by ac_rfl
  have h10 : 12*x*x = 12*(x*x) := by ac_rfl
  have h11 : 8*x*x = 8*(x*x) := by ac_rfl
  omega

private def topOneCellDriftClosed (D n : Nat) : Int :=
  let d : Int := Int.ofNat D
  let a : Int := Int.ofNat n
  0 - 8 * d * a + 32 * a * a * a + 12 * a * a - 8 * a

private def reverseTopOneClosed (D n c : Nat) : Int :=
  let d : Int := Int.ofNat D
  let a : Int := Int.ofNat n
  let b : Int := Int.ofNat (n + c)
  4 * d * (b * b + b + a * a - a) -
      8 * b * b * b * b - 12 * b * b * b + 2 * b * b + 6 * b -
      8 * a * a * a * a + 12 * a * a * a + 2 * a * a - 6 * a

private theorem reverseTopOneClosed_step (D n c : Nat) :
    reverseTopOneClosed D n (c + 1) =
      topOneCellDriftClosed D n + reverseTopOneClosed D (n + 1) c := by
  unfold reverseTopOneClosed topOneCellDriftClosed
  simp only [Nat.add_left_comm, Nat.add_comm, Int.ofNat_eq_natCast,
    Int.natCast_add, Int.mul_add, Int.add_mul, Int.sub_eq_add_neg, Int.neg_add]
  have h1 : ((1 : Nat) : Int) = (1 : Int) := rfl
  rw [h1]
  simp only [Int.one_mul, Int.mul_one]
  have hD : 8 * (D : Int) * (n : Int) =
      2 * (4 * (D : Int) * (n : Int)) := by ac_rfl
  have hn3 : 32 * (n : Int) * (n : Int) * (n : Int) =
      4 * (8 * (n : Int) * (n : Int) * (n : Int)) := by ac_rfl
  have hn2 : 4 * (12 * (n : Int) * (n : Int)) =
      6 * (8 * (n : Int) * (n : Int)) := by ac_rfl
  omega

private theorem topOne_cell_drift (D n : Nat) (hnpos : 0 < n)
    (hdiag : 2 * n * n + 1 ≤ D)
    (hoff : 2 * n * (n + 1) - 1 ≤ D) :
    diagCoeff D n (D - 1) - offCoeff D n (D - 1) =
      topOneCellDriftClosed D n := by
  have hDpos : 0 < D := by omega
  rw [diagCoeff_top_one hnpos hdiag, offCoeff_top_one hDpos hoff]
  have hsquare : 1 ≤ n * n := Nat.mul_le_mul hnpos hnpos
  have h16 : 16 * n * n ≤ 8 * D := by
    simp only [Nat.mul_assoc] at hdiag ⊢
    omega
  have hexp : 1 ≤ 2 * n * (n + 1) := by
    have hn1pos : 1 ≤ n + 1 := by omega
    have hmul : 1 * 1 ≤ n * (n + 1) := Nat.mul_le_mul hnpos hn1pos
    have : 1 ≤ n * (n + 1) := by simpa using hmul
    simp only [Nat.mul_assoc] at ⊢
    omega
  have hdiagCast : Int.ofNat (topOneDiagNat D n) =
      (n : Int) * (n : Int) *
        (8 * (D : Int) - 16 * (n : Int) * (n : Int) + 4) := by
    unfold topOneDiagNat
    simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add]
    rw [Int.natCast_sub h16]
    rfl
  have hoffCast : Int.ofNat (topOneOffNat D n) =
      8 * (n : Int) * ((n : Int) + 1) *
        ((D : Int) - (2 * (n : Int) * ((n : Int) + 1) - 1)) := by
    unfold topOneOffNat
    simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add]
    rw [Int.natCast_sub hoff, Int.natCast_sub hexp]
    rfl
  rw [hdiagCast, hoffCast]
  unfold topOneCellDriftClosed
  exact top_one_algebra (n : Int) (D : Int)

private theorem reverse_top_one_zero_algebra (x d : Int) :
    4 * d * (x * x + x + x * x - x) -
        8 * x * x * x * x - 12 * x * x * x + 2 * x * x + 6 * x -
        8 * x * x * x * x + 12 * x * x * x + 2 * x * x - 6 * x =
      x * x * (8 * d - 16 * x * x + 4) := by
  simp only [Int.mul_add, Int.sub_eq_add_neg, Int.mul_neg]
  let z1 := x * x * d
  let z2 := x * x * x * x
  let z3 := x * x
  have h1a : 4*d*(x*x) = 4*z1 := by dsimp [z1]; ac_rfl
  have h1b : x*x*(8*d) = 8*z1 := by dsimp [z1]; ac_rfl
  have h1 : 4*d*(x*x) + 4*d*(x*x) = x*x*(8*d) := by omega
  have h2a : 8*x*x*x*x = 8*z2 := by dsimp [z2]; ac_rfl
  have h2b : x*x*(16*x*x) = 16*z2 := by dsimp [z2]; ac_rfl
  have h2 : 8*x*x*x*x + 8*x*x*x*x = x*x*(16*x*x) := by omega
  have h3a : 2*x*x = 2*z3 := by dsimp [z3]; ac_rfl
  have h3b : x*x*4 = 4*z3 := by dsimp [z3]; ac_rfl
  have h3 : 2*x*x + 2*x*x = x*x*4 := by omega
  omega

private theorem reverseTopOneClosed_zero (D n : Nat) :
    reverseTopOneClosed D n 0 =
      (n : Int) * (n : Int) *
        (8 * (D : Int) - 16 * (n : Int) * (n : Int) + 4) := by
  unfold reverseTopOneClosed
  simp only [Nat.add_zero]
  exact reverse_top_one_zero_algebra (n : Int) (D : Int)

/-- Exact deficit-one coefficient of an arbitrary reverse tail. -/
theorem reverseTailCoeff_top_one (D n c : Nat) (hnpos : 0 < n)
    (hD : 2 * (n + c) * (n + c) + 1 ≤ D) :
    reverseTailCoeff D n (D - 1) c = reverseTopOneClosed D n c := by
  induction c generalizing n with
  | zero =>
      simp only [Nat.add_zero] at hD
      rw [reverseTailCoeff]
      rw [diagCoeff_top_one hnpos (by simpa using hD)]
      rw [reverseTopOneClosed_zero]
      unfold topOneDiagNat
      have hsquare : 1 ≤ n * n := Nat.mul_le_mul hnpos hnpos
      have h16 : 16 * n * n ≤ 8 * D := by
        simp only [Nat.mul_assoc] at hD ⊢
        omega
      simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add]
      rw [Int.natCast_sub h16]
      simp only [Int.natCast_mul]
      have h4 : ((4 : Nat) : Int) = (4 : Int) := rfl
      have h8 : ((8 : Nat) : Int) = (8 : Int) := rfl
      have h16' : ((16 : Nat) : Int) = (16 : Int) := rfl
      rw [h4, h8, h16']
  | succ c ih =>
      rw [reverseTailCoeff]
      have hnle : n ≤ n + (c + 1) := by omega
      have hn1le : n + 1 ≤ n + (c + 1) := by omega
      have hsquare : n * n ≤ (n + (c + 1)) * (n + (c + 1)) :=
        Nat.mul_le_mul hnle hnle
      have hrect : n * (n + 1) ≤ (n + (c + 1)) * (n + (c + 1)) :=
        Nat.mul_le_mul hnle hn1le
      have hn : 2 * n * n + 1 ≤ D := by
        simp only [Nat.mul_assoc] at hD ⊢
        omega
      have hoff : 2 * n * (n + 1) - 1 ≤ D := by
        simp only [Nat.mul_assoc] at hD ⊢
        omega
      rw [topOne_cell_drift D n hnpos hn hoff]
      rw [ih (n + 1) (by omega) (by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hD)]
      exact (reverseTopOneClosed_step D n c).symm

/-- At minimal supported degree, the start-one deficit-one base value is
`-2m(m+1)(2m-5)`. -/
theorem minimalBase_deficit_one (m : Nat) (hm : 0 < m) :
    reverseTailCoeff (2 * m * m + 1) 1 (2 * m * m) (m - 1) =
      -(2 * (m : Int) * ((m : Int) + 1) * (2 * (m : Int) - 5)) := by
  have htop := reverseTailCoeff_top_one (2 * m * m + 1) 1 (m - 1) (by omega) (by
    have hm' : 1 + (m - 1) = m := by omega
    rw [hm']
    omega
  )
  have hidx : 2 * m * m + 1 - 1 = 2 * m * m := by omega
  rw [hidx] at htop
  rw [htop]
  unfold reverseTopOneClosed
  have hm' : 1 + (m - 1) = m := by omega
  rw [hm']
  simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul]
  have h1 : ((1 : Nat) : Int) = (1 : Int) := rfl
  rw [h1]
  simp only [Int.mul_one]
  let x : Int := (m : Int)
  have h2m : ((2 : Nat) : Int) * x * x = 2 * x * x := by rfl
  change
    4 * (2 * x * x + 1) * (x * x + x + 1 * 1 - 1) -
          8 * x * x * x * x - 12 * x * x * x + 2 * x * x + 6 * x -
          8 * 1 * 1 * 1 * 1 + 12 * 1 * 1 * 1 + 2 * 1 * 1 - 6 * 1 =
      -(2 * x * (x + 1) * (2 * x - 5))
  simp only [Int.mul_one]
  simp only [Int.mul_add, Int.add_mul, Int.sub_eq_add_neg, Int.neg_add,
    Int.mul_neg]
  have hA : 4 * (2*x*x) * (x*x) = 8*x*x*x*x := by ac_rfl
  have hB : 4 * (2*x*x) * x = 8*x*x*x := by ac_rfl
  have hC : 2*x*(x+1)*(2*x) = 4*x*x*x + 4*x*x := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_one]
    let z2 := x*x
    let z3 := x*x*x
    have hC1 : 2*x*x*(2*x) = 4*z3 := by dsimp [z3]; ac_rfl
    have hC2 : 2*x*1*(2*x) = 4*z2 := by dsimp [z2]; ac_rfl
    have hC3 : 4*x*x*x = 4*z3 := by dsimp [z3]; ac_rfl
    have hC4 : 2*x*(2*x) = 4*z2 := by dsimp [z2]; ac_rfl
    have hC5 : 4*x*x = 4*z2 := by dsimp [z2]; ac_rfl
    omega
  let z2 := x*x
  let z3 := x*x*x
  have hD1 : 4*(2*x*x) = 8*z2 := by dsimp [z2]; ac_rfl
  have hD2 : 8*x*x*x = 8*z3 := by dsimp [z3]; ac_rfl
  have hD3 : 12*x*x*x = 12*z3 := by dsimp [z3]; ac_rfl
  have hD4 : 4*x*x*x = 4*z3 := by dsimp [z3]; ac_rfl
  have hD5 : 4*x*x = 4*z2 := by dsimp [z2]; ac_rfl
  have hD6 : 4*(x*x) = 4*z2 := by dsimp [z2]
  have hC' : 2*x*x*(2*x) + 2*x*1*(2*x) = 4*z3 + 4*z2 := by
    have hC1 : 2*x*x*(2*x) = 4*z3 := by dsimp [z3]; ac_rfl
    have hC2 : 2*x*1*(2*x) = 4*z2 := by dsimp [z2]; ac_rfl
    omega
  omega

/-- The minimal deficit-one base is strictly negative from terminal cell
three onward.  This fences a fully nonnegative minimal Pascal row. -/
theorem minimalBase_deficit_one_negative (m : Nat) (hm : 3 ≤ m) :
    reverseTailCoeff (2 * m * m + 1) 1 (2 * m * m) (m - 1) < 0 := by
  rw [minimalBase_deficit_one m (by omega)]
  have hx3 : (3 : Int) ≤ (m : Int) := Int.ofNat_le.mpr hm
  have h2 : (0 : Int) < 2 := by decide
  have hm0 : (0 : Int) < (m : Int) := by omega
  have hm1 : (0 : Int) < (m : Int) + 1 := by omega
  have hf : (0 : Int) < 2 * (m : Int) - 5 := by omega
  have h2m : (0 : Int) < 2 * (m : Int) := Int.mul_pos h2 hm0
  have h2m1 : (0 : Int) < 2 * (m : Int) * ((m : Int) + 1) :=
    Int.mul_pos h2m hm1
  have hp : (0 : Int) <
      2 * (m : Int) * ((m : Int) + 1) * (2 * (m : Int) - 5) :=
    Int.mul_pos h2m1 hf
  omega

/-! The second boundary coordinate is handled in doubled form, avoiding any
division in the constructive substrate. -/

private theorem two_choose_pred_pred : ∀ q : Nat,
    2 * Int.ofNat (PNPaths.choose (q + 2) q) =
      Int.ofNat ((q + 2) * (q + 1))
  | 0 => by decide
  | q + 1 => by
      change 2 * Int.ofNat (PNPaths.choose ((q + 2) + 1) (q + 1)) =
        Int.ofNat (((q + 1) + 2) * ((q + 1) + 1))
      rw [PNPaths.choose]
      simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul]
      rw [Int.mul_add]
      have hi := two_choose_pred_pred q
      simp only [Int.ofNat_eq_natCast] at hi
      rw [hi, choose_pred (q + 1)]
      have hnat : (q + 2) * (q + 1) + 2 * (q + 2) =
          (q + 3) * (q + 2) := by
        simp only [Nat.mul_add, Nat.add_mul]
        omega
      have hint := congrArg Int.ofNat hnat
      simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul] at hint
      simpa only [Nat.add_assoc] using hint

private theorem six_choose_pred_pred_pred : ∀ q : Nat,
    6 * Int.ofNat (PNPaths.choose (q + 3) q) =
      Int.ofNat ((q + 3) * (q + 2) * (q + 1))
  | 0 => by decide
  | q + 1 => by
      change 6 * Int.ofNat (PNPaths.choose ((q + 3) + 1) (q + 1)) =
        Int.ofNat (((q + 1) + 3) * ((q + 1) + 2) * ((q + 1) + 1))
      rw [PNPaths.choose]
      simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul]
      rw [Int.mul_add]
      have hi := six_choose_pred_pred_pred q
      simp only [Int.ofNat_eq_natCast] at hi
      rw [hi]
      have htwo := two_choose_pred_pred (q + 1)
      simp only [Int.ofNat_eq_natCast] at htwo
      have hq3 : q+1+2=q+3 := by omega
      have hq2 : q+1+1=q+2 := by omega
      rw [hq3,hq2] at htwo
      have hsix : 6 * (PNPaths.choose (q + 3) (q + 1):Int) =
          3 * (((q + 3) * (q + 2):Nat):Int) := by
        have h := congrArg (fun z : Int => 3 * z) htwo
        rw [show (6:Int)=3*2 by decide]
        simpa only [Int.mul_assoc] using h
      rw [hsix]
      have hnat : (q+3)*(q+2)*(q+1)+3*((q+3)*(q+2)) =
          (q+4)*(q+3)*(q+2) := by
        calc
          (q+3)*(q+2)*(q+1)+3*((q+3)*(q+2)) =
              ((q+3)*(q+2))*(q+1)+((q+3)*(q+2))*3 := by ac_rfl
          _ = ((q+3)*(q+2))*((q+1)+3) := by
            exact (Nat.mul_add _ _ _).symm
          _ = (q+4)*(q+3)*(q+2) := by
            rw [show q+4=(q+1)+3 by omega]
            ac_rfl
      have hint := congrArg Int.ofNat hnat
      simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul] at hint
      simpa only [Nat.add_assoc] using hint

private theorem two_mul_monoCoeff_top_two {D e : Nat} (hD2 : 2 ≤ D)
    (heD : e ≤ D) :
    2 * monoCoeff D e (D - 2) =
      Int.ofNat ((D - e) * (D - e - 1)) := by
  by_cases he : e ≤ D - 2
  · simp only [monoCoeff, if_pos he]
    have harg : D - 2 - e = (D - e) - 2 := by omega
    rw [harg]
    cases hq : D - e with
    | zero => omega
    | succ q =>
        cases q with
        | zero => omega
        | succ q =>
            have hqsub : q + 1 + 1 - 2 = q := by omega
            rw [hqsub, two_choose_pred_pred q]
            congr 1
  · simp only [monoCoeff, if_neg he]
    have hsmall : D - e ≤ 1 := by omega
    by_cases hz : D - e = 0
    · simp [hz]
    · have ho : D - e = 1 := by omega
      simp [ho]

/-- Cleared exact third-deficit coefficient of one Bernstein monomial. -/
private theorem six_mul_monoCoeff_top_three {D e : Nat} (hD3 : 3 ≤ D)
    (heD : e ≤ D) :
    6 * monoCoeff D e (D - 3) =
      Int.ofNat ((D-e)*(D-e-1)*(D-e-2)) := by
  by_cases he : e ≤ D-3
  · simp only [monoCoeff, if_pos he]
    have harg : D-3-e=(D-e)-3 := by omega
    rw [harg]
    cases hq : D-e with
    | zero => omega
    | succ q =>
        cases q with
        | zero => omega
        | succ q =>
            cases q with
            | zero => omega
            | succ q =>
                have hqsub : q+1+1+1-3=q := by omega
                rw [hqsub,six_choose_pred_pred_pred q]
                congr 1
  · simp only [monoCoeff, if_neg he]
    have hsmall : D-e≤2 := by omega
    by_cases hz : D-e=0
    · simp [hz]
    · by_cases ho : D-e=1
      · simp [ho]
      · have ht : D-e=2 := by omega
        simp [ht]

/-- Cleared cubic falling-factorial atom for the third deficit. -/
def topThreeMonoClosed (D e : Nat) : Int :=
  Int.ofNat ((D-e)*(D-e-1)*(D-e-2))

/-- Cleared diagonal contribution at deficit three. -/
def topThreeDiagClosed (D n : Nat) : Int :=
  Int.ofNat (n*n) *
    (topThreeMonoClosed D (2*n*n-2) +
      3*topThreeMonoClosed D (2*n*n-1) +
      3*topThreeMonoClosed D (2*n*n) +
      topThreeMonoClosed D (2*n*n+1))

/-- Cleared off-diagonal contribution at deficit three. -/
def topThreeOffClosed (D n : Nat) : Int :=
  Int.ofNat (8*n*(n+1))*topThreeMonoClosed D (2*n*(n+1)-1)

/-- Cleared arbitrary reverse suffix at deficit three. -/
def reverseTopThreeClosed (D n : Nat) : Nat → Int
  | 0 => topThreeDiagClosed D n
  | c+1 => topThreeDiagClosed D n-topThreeOffClosed D n+
      reverseTopThreeClosed D (n+1) c

private theorem six_mul_diagCoeff_top_three (D n : Nat)
    (hD3 : 3≤D) (hdiag : 2*n*n+1≤D) :
    6*diagCoeff D n (D-3)=topThreeDiagClosed D n := by
  unfold diagCoeff topThreeDiagClosed topThreeMonoClosed
  have h0 : 2*n*n-2≤D := by omega
  have h1 : 2*n*n-1≤D := by omega
  have h2 : 2*n*n≤D := by omega
  have hm0 := six_mul_monoCoeff_top_three hD3 h0
  have hm1 := six_mul_monoCoeff_top_three hD3 h1
  have hm2 := six_mul_monoCoeff_top_three hD3 h2
  have hm3 := six_mul_monoCoeff_top_three hD3 hdiag
  simp only [Int.ofNat_eq_natCast] at hm0 hm1 hm2 hm3 ⊢
  simp only [Int.mul_add]
  have t0 : 6*(((n*n:Nat):Int)*monoCoeff D (2*n*n-2) (D-3)) =
      ((n*n:Nat):Int)*(((D-(2*n*n-2))*(D-(2*n*n-2)-1)*
        (D-(2*n*n-2)-2):Nat):Int) := by
    rw [show 6*(((n*n:Nat):Int)*monoCoeff D (2*n*n-2) (D-3)) =
      ((n*n:Nat):Int)*(6*monoCoeff D (2*n*n-2) (D-3)) by ac_rfl,hm0]
  have t1 : 6*(((n*n:Nat):Int)*(3*monoCoeff D (2*n*n-1) (D-3))) =
      ((n*n:Nat):Int)*(3*(((D-(2*n*n-1))*(D-(2*n*n-1)-1)*
        (D-(2*n*n-1)-2):Nat):Int)) := by
    rw [show 6*(((n*n:Nat):Int)*(3*monoCoeff D (2*n*n-1) (D-3))) =
      ((n*n:Nat):Int)*(3*(6*monoCoeff D (2*n*n-1) (D-3))) by ac_rfl,hm1]
  have t2 : 6*(((n*n:Nat):Int)*(3*monoCoeff D (2*n*n) (D-3))) =
      ((n*n:Nat):Int)*(3*(((D-2*n*n)*(D-2*n*n-1)*
        (D-2*n*n-2):Nat):Int)) := by
    rw [show 6*(((n*n:Nat):Int)*(3*monoCoeff D (2*n*n) (D-3))) =
      ((n*n:Nat):Int)*(3*(6*monoCoeff D (2*n*n) (D-3))) by ac_rfl,hm2]
  have t3 : 6*(((n*n:Nat):Int)*monoCoeff D (2*n*n+1) (D-3)) =
      ((n*n:Nat):Int)*(((D-(2*n*n+1))*(D-(2*n*n+1)-1)*
        (D-(2*n*n+1)-2):Nat):Int) := by
    rw [show 6*(((n*n:Nat):Int)*monoCoeff D (2*n*n+1) (D-3)) =
      ((n*n:Nat):Int)*(6*monoCoeff D (2*n*n+1) (D-3)) by ac_rfl,hm3]
  rw [t0,t1,t2,t3]

private theorem six_mul_offCoeff_top_three (D n : Nat)
    (hD3 : 3≤D) (hoff : 2*n*(n+1)-1≤D) :
    6*offCoeff D n (D-3)=topThreeOffClosed D n := by
  unfold offCoeff topThreeOffClosed topThreeMonoClosed
  have hm := six_mul_monoCoeff_top_three hD3 hoff
  simp only [Int.ofNat_eq_natCast] at hm ⊢
  rw [show 6*(((8*n*(n+1):Nat):Int)*
      monoCoeff D (2*n*(n+1)-1) (D-3)) =
    ((8*n*(n+1):Nat):Int)*(6*monoCoeff D (2*n*(n+1)-1) (D-3)) by ac_rfl]
  rw [hm]

/-- Exact arbitrary reverse-suffix formula at deficit three, cleared by six. -/
theorem six_mul_reverseTailCoeff_top_three (D n c : Nat) (hnpos : 0<n)
    (hD : 2*(n+c)*(n+c)+1≤D) :
    6*reverseTailCoeff D n (D-3) c=reverseTopThreeClosed D n c := by
  have hD3 : 3≤D := by
    have hp : 1≤n+c := by omega
    have hs : 1≤(n+c)*(n+c) := Nat.mul_le_mul hp hp
    simp only [Nat.mul_assoc] at hD ⊢
    omega
  induction c generalizing n with
  | zero =>
      simp only [reverseTailCoeff,reverseTopThreeClosed]
      exact six_mul_diagCoeff_top_three D n hD3 (by simpa using hD)
  | succ c ih =>
      simp only [reverseTailCoeff,reverseTopThreeClosed]
      have hnle : n≤n+(c+1) := by omega
      have hn1le : n+1≤n+(c+1) := by omega
      have hsquare : n*n≤(n+(c+1))*(n+(c+1)) := Nat.mul_le_mul hnle hnle
      have hrect : n*(n+1)≤(n+(c+1))*(n+(c+1)) := Nat.mul_le_mul hnle hn1le
      have hd : 2*n*n+1≤D := by
        simp only [Nat.mul_assoc] at hD ⊢
        omega
      have ho : 2*n*(n+1)-1≤D := by
        simp only [Nat.mul_assoc] at hD ⊢
        omega
      rw [Int.mul_add,Int.mul_sub]
      rw [six_mul_diagCoeff_top_three D n hD3 hd,
        six_mul_offCoeff_top_three D n hD3 ho]
      rw [ih (n+1) (by omega) (by
        simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hD)]

/-- Append one terminal cell to the cleared third-deficit reverse suffix. -/
theorem reverseTopThreeClosed_append (D n c : Nat) :
    reverseTopThreeClosed D n (c+1) =
      reverseTopThreeClosed D n c-topThreeOffClosed D (n+c)+
        topThreeDiagClosed D (n+c+1) := by
  induction c generalizing n with
  | zero => simp [reverseTopThreeClosed]
  | succ c ih =>
      change topThreeDiagClosed D n-topThreeOffClosed D n+
          reverseTopThreeClosed D (n+1) (c+1) =
        (topThreeDiagClosed D n-topThreeOffClosed D n+
          reverseTopThreeClosed D (n+1) c)-topThreeOffClosed D (n+(c+1))+
            topThreeDiagClosed D (n+(c+1)+1)
      rw [ih (n+1)]
      simp only [Int.sub_eq_add_neg]
      ac_rfl

private def intFallThree (z : Int) : Int := z*(z-1)*(z-2)

private theorem topThreeMonoClosed_cast {D e : Nat} (he : e+2≤D) :
    topThreeMonoClosed D e=intFallThree ((D:Int)-(e:Int)) := by
  unfold topThreeMonoClosed intFallThree
  simp only [Int.ofNat_eq_natCast,Int.natCast_mul]
  rw [Int.natCast_sub (by omega : e≤D)]
  rw [Int.natCast_sub (by omega : 1≤D-e)]
  rw [Int.natCast_sub (by omega : 2≤D-e)]
  have h1 : ((1:Nat):Int)=(1:Int) := rfl
  have h2 : ((2:Nat):Int)=(2:Int) := rfl
  rw [h1,h2]
  have hde : ((D-e:Nat):Int)=(D:Int)-(e:Int) :=
    Int.natCast_sub (by omega)
  rw [hde]

/-- Cleared third-deficit drift of the first individual cell. -/
def firstCellThreeDrift (D : Nat) : Int :=
  topThreeDiagClosed D 1-topThreeOffClosed D 1

private theorem first_cell_three_algebra (d : Int) :
    intFallThree d+3*intFallThree (d-1)+3*intFallThree (d-2)-
        15*intFallThree (d-3) =
      -8*d*d*d+132*d*d-592*d+810 := by
  unfold intFallThree
  simp only [Int.sub_mul,Int.mul_sub,Int.add_mul,Int.mul_add]
  simp only [Int.mul_assoc]
  have h1:d*(1*d)=d*d:=by ac_rfl
  have h2:d*(d*2)=2*(d*d):=by ac_rfl
  have h3:d*(d*1)=d*d:=by ac_rfl
  have h4:d*(2*d)=2*(d*d):=by ac_rfl
  have h5:d*(3*d)=3*(d*d):=by ac_rfl
  have h6:d*(d*3)=3*(d*d):=by ac_rfl
  rw[h1,h2,h3,h4,h5,h6]
  omega

/-- Exact parametric fence: the first cell's cleared third-deficit drift is
already negative once the degree reaches eleven. -/
theorem firstCellThreeDrift_eq (D : Nat) (hD : 11≤D) :
    firstCellThreeDrift D =
      -8*(D:Int)*(D:Int)*(D:Int)+132*(D:Int)*(D:Int)-592*(D:Int)+810 := by
  unfold firstCellThreeDrift topThreeDiagClosed topThreeOffClosed
  simp only [Nat.one_mul,Nat.mul_one,Nat.one_add]
  rw [show 2-2=0 by decide,show 2-1=1 by decide,
    show 2+1=3 by decide,show 8*Nat.succ 1=16 by decide,
    show 2*Nat.succ 1-1=3 by decide]
  simp only [Int.ofNat_eq_natCast]
  have h1 : ((1:Nat):Int)=(1:Int) := rfl
  have h0 : ((0:Nat):Int)=(0:Int) := rfl
  have h2 : ((2:Nat):Int)=(2:Int) := rfl
  have h3 : ((3:Nat):Int)=(3:Int) := rfl
  have h16 : ((16:Nat):Int)=(16:Int) := rfl
  rw [h1,h16]
  simp only [Int.one_mul]
  rw [topThreeMonoClosed_cast (D:=D) (e:=0) (by omega),
    topThreeMonoClosed_cast (D:=D) (e:=1) (by omega),
    topThreeMonoClosed_cast (D:=D) (e:=2) (by omega),
    topThreeMonoClosed_cast (D:=D) (e:=3) (by omega)]
  rw [h0,h1,h2,h3]
  rw [Int.sub_zero]
  have ha := first_cell_three_algebra (D:Int)
  omega

/-- Thus no proof of the target third-deficit suffix can proceed by requiring
each paired cell drift to be nonnegative. -/
theorem firstCellThreeDrift_negative (D : Nat) (hD : 11≤D) :
    firstCellThreeDrift D<0 := by
  rw [firstCellThreeDrift_eq D hD]
  let u : Int := (D:Int)-11
  have hu : 0≤u := by
    dsimp [u]
    have hc : (11:Int)≤(D:Int) := Int.ofNat_le.mpr hD
    omega
  have hd : (D:Int)=u+11 := by dsimp [u]; omega
  rw [hd]
  have hu2 : 0≤u*u := Int.mul_nonneg hu hu
  have hu3 : 0≤u*u*u := Int.mul_nonneg hu2 hu
  have hexpand : -8*(u+11)*(u+11)*(u+11)+132*(u+11)*(u+11)-
      592*(u+11)+810 = -8*(u*u*u)-132*(u*u)-592*u-378 := by
    simp only [Int.mul_add,Int.add_mul]
    simp only [Int.mul_assoc]
    have h1:u*(11*u)=11*(u*u):=by ac_rfl
    have h2:u*(u*11)=11*(u*u):=by ac_rfl
    have h3:u*(u*u)=u*u*u:=by ac_rfl
    rw [h1,h2,h3]
    omega
  rw [hexpand]
  omega

private theorem top_two_diag_algebra (x y : Int) :
    x*x*((y+2)*(y+1)+3*((y+1)*y)+3*(y*(y-1))+(y-1)*(y-2)) =
      2*(4*x*x*y*y+2*x*x) := by
  simp only [Int.mul_add, Int.add_mul, Int.sub_eq_add_neg, Int.neg_add,
    Int.mul_neg]
  simp only [Int.one_mul, Int.mul_one, Int.neg_mul]
  let z := x*x*y*y
  let u := x*x
  have h1 : x*x*(y*y) = z := by dsimp [z]; ac_rfl
  have h2 : x*x*(2*y) = 2*(x*x*y) := by ac_rfl
  have h2b : x*x*(y*2) = 2*(x*x*y) := by ac_rfl
  have hn : x*x*(-y) = -(x*x*y) := by rw [Int.mul_neg]
  have h3 : x*x*(3*(y*y)) = 3*z := by dsimp [z]; ac_rfl
  have h4 : x*x*(3*y) = 3*(x*x*y) := by ac_rfl
  have h5 : x*x*2 = 2*u := by dsimp [u]; ac_rfl
  have h6 : 2*(4*x*x*y*y) = 8*z := by dsimp [z]; ac_rfl
  have h7 : 2*(2*x*x) = 4*u := by dsimp [u]; ac_rfl
  omega

private theorem pred_pred_product_cast (y : Nat) (hy : 1 ≤ y) :
    Int.ofNat ((y-1)*(y-1-1)) = ((y:Int)-1)*((y:Int)-2) := by
  by_cases hyEqOne : y = 1
  · subst y
    decide
  · have hyTwo : 2 ≤ y := by omega
    have hsub : y-1-1=y-2 := by omega
    rw [hsub]
    simp only [Int.ofNat_eq_natCast, Int.natCast_mul]
    rw [Int.natCast_sub (by omega : 1 ≤ y),
      Int.natCast_sub (by omega : 2 ≤ y)]
    have h1c : ((1 : Nat) : Int) = (1 : Int) := rfl
    have h2c : ((2 : Nat) : Int) = (2 : Int) := rfl
    rw [h1c, h2c]

private theorem pred_product_cast (z : Nat) :
    Int.ofNat (z*(z-1)) = (z:Int)*((z:Int)-1) := by
  cases z with
  | zero => decide
  | succ q =>
      simp only [Nat.add_sub_cancel, Int.ofNat_eq_natCast, Int.natCast_mul,
        Int.natCast_add]
      have h1 : ((1 : Nat) : Int) = (1 : Int) := rfl
      rw [h1]
      have hs : (q : Int) + 1 - 1 = (q : Int) := by omega
      rw [hs]

private theorem two_mul_diagCoeff_top_two {D n : Nat} (hnpos : 0 < n)
    (hD : 2 * n * n + 1 ≤ D) :
    2 * diagCoeff D n (D - 2) =
      2 * (4 * (n : Int) * (n : Int) *
          ((D : Int) - 2 * (n : Int) * (n : Int)) *
          ((D : Int) - 2 * (n : Int) * (n : Int)) +
        2 * (n : Int) * (n : Int)) := by
  have hsquare : 1 ≤ n * n := Nat.mul_le_mul hnpos hnpos
  have hD2 : 2 ≤ D := by
    simp only [Nat.mul_assoc] at hD ⊢
    omega
  have h0 : 2 * n * n - 2 ≤ D := by omega
  have h1 : 2 * n * n - 1 ≤ D := by omega
  have h2 : 2 * n * n ≤ D := by omega
  have hm0 := two_mul_monoCoeff_top_two hD2 h0
  have hm1 := two_mul_monoCoeff_top_two hD2 h1
  have hm2 := two_mul_monoCoeff_top_two hD2 h2
  have hm3 := two_mul_monoCoeff_top_two hD2 hD
  have hrearr :
      2 * diagCoeff D n (D - 2) =
        (n : Int) * (n : Int) *
          (2 * monoCoeff D (2*n*n-2) (D-2) +
            3 * (2 * monoCoeff D (2*n*n-1) (D-2)) +
            3 * (2 * monoCoeff D (2*n*n) (D-2)) +
            2 * monoCoeff D (2*n*n+1) (D-2)) := by
    unfold diagCoeff
    simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.mul_add]
    ac_rfl
  rw [hrearr, hm0, hm1, hm2, hm3]
  let y := D - 2*n*n
  have hy0 : D - (2*n*n-2) = y+2 := by
    dsimp [y]
    simp only [Nat.mul_assoc] at hD ⊢
    omega
  have hy1 : D - (2*n*n-1) = y+1 := by dsimp [y]; omega
  have hy2 : D - 2*n*n = y := by rfl
  have hy3 : D - (2*n*n+1) = y-1 := by dsimp [y]; omega
  rw [hy0, hy1, hy2, hy3]
  have hypos : 1 ≤ y := by dsimp [y]; omega
  have h1c : ((1 : Nat) : Int) = (1 : Int) := rfl
  have h2c : ((2 : Nat) : Int) = (2 : Int) := rfl
  have hp0 : Int.ofNat ((y+2)*(y+2-1)) =
      ((y:Int)+2)*((y:Int)+1) := by
    have : y+2-1=y+1 := by omega
    rw [this]
    simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add]
    rfl
  have hp1 : Int.ofNat ((y+1)*(y+1-1)) =
      ((y:Int)+1)*(y:Int) := by
    have : y+1-1=y := by omega
    rw [this]
    simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add]
    rfl
  have hp2 : Int.ofNat (y*(y-1)) =
      (y:Int)*((y:Int)-1) := by
    simp only [Int.ofNat_eq_natCast, Int.natCast_mul]
    rw [Int.natCast_sub hypos]
    rw [h1c]
  have hp3 := pred_pred_product_cast y hypos
  rw [hp0, hp1, hp2, hp3]
  have hycast : (y : Int) = (D : Int) - 2*(n : Int)*(n : Int) := by
    dsimp [y]
    rw [Int.natCast_sub (by omega : 2*n*n ≤ D)]
    simp only [Int.natCast_mul]
    rfl
  rw [← hycast]
  exact top_two_diag_algebra (n : Int) (y : Int)

private theorem two_mul_offCoeff_top_two {D n : Nat} (hnpos : 0 < n)
    (hD2 : 2 ≤ D) (hD : 2 * n * (n + 1) - 1 ≤ D) :
    2 * offCoeff D n (D - 2) =
      2 * (4 * (n : Int) * ((n : Int) + 1) *
        ((D : Int) - (2 * (n : Int) * ((n : Int) + 1) - 1)) *
        ((D : Int) - (2 * (n : Int) * ((n : Int) + 1) - 1) - 1)) := by
  have hm := two_mul_monoCoeff_top_two hD2 hD
  have hrearr : 2 * offCoeff D n (D - 2) =
      8 * (n : Int) * ((n : Int) + 1) *
        (2 * monoCoeff D (2*n*(n+1)-1) (D-2)) := by
    unfold offCoeff
    simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add,
      Int.mul_add]
    have h1 : ((1 : Nat) : Int) = (1 : Int) := rfl
    have h8 : ((8 : Nat) : Int) = (8 : Int) := rfl
    rw [h1, h8]
    ac_rfl
  rw [hrearr, hm]
  let z := D - (2*n*(n+1)-1)
  have hz : D - (2*n*(n+1)-1) = z := rfl
  rw [hz]
  have hzcast : (z : Int) =
      (D : Int) - (2 * (n : Int) * ((n : Int) + 1) - 1) := by
    dsimp [z]
    rw [Int.natCast_sub hD]
    have hexp : 1 ≤ 2*n*(n+1) := by
      have hn1 : 1 ≤ n+1 := by omega
      have hp : 1*1 ≤ n*(n+1) := Nat.mul_le_mul hnpos hn1
      simp only [Nat.mul_assoc] at ⊢
      omega
    rw [Int.natCast_sub hexp]
    simp only [Int.natCast_mul, Int.natCast_add]
    have h1 : ((1 : Nat) : Int) = (1 : Int) := rfl
    have h2 : ((2 : Nat) : Int) = (2 : Int) := rfl
    rw [h1, h2]
  simp only [Int.ofNat_eq_natCast]
  have hp := pred_product_cast z
  simp only [Int.ofNat_eq_natCast] at hp
  rw [hp, hzcast]
  rw [show (8 : Int) = 2 * 4 by decide]
  ac_rfl

/-- Exact doubled deficit-two drift of one cell, in division-free form. -/
theorem two_mul_topTwo_cell_drift (D n : Nat) (hnpos : 0 < n)
    (hdiag : 2 * n * n + 1 ≤ D)
    (hoff : 2 * n * (n + 1) - 1 ≤ D) :
    2 * (diagCoeff D n (D - 2) - offCoeff D n (D - 2)) =
      2 * ((4 * (n : Int) * (n : Int) *
          ((D : Int) - 2 * (n : Int) * (n : Int)) *
          ((D : Int) - 2 * (n : Int) * (n : Int)) +
        2 * (n : Int) * (n : Int)) -
        (4 * (n : Int) * ((n : Int) + 1) *
          ((D : Int) - (2 * (n : Int) * ((n : Int) + 1) - 1)) *
          ((D : Int) - (2 * (n : Int) * ((n : Int) + 1) - 1) - 1))) := by
  have hD2 : 2 ≤ D := by
    have hsquare : 1 ≤ n*n := Nat.mul_le_mul hnpos hnpos
    simp only [Nat.mul_assoc] at hdiag ⊢
    omega
  rw [Int.mul_sub]
  rw [two_mul_diagCoeff_top_two hnpos hdiag]
  rw [two_mul_offCoeff_top_two hnpos hD2 hoff]
  rw [← Int.mul_sub]

/-- Division-free closed diagonal at deficit two. -/
def topTwoDiagClosed (D n : Nat) : Int :=
  4 * (n : Int) * (n : Int) *
      ((D : Int) - 2 * (n : Int) * (n : Int)) *
      ((D : Int) - 2 * (n : Int) * (n : Int)) +
    2 * (n : Int) * (n : Int)

/-- Division-free closed off-diagonal at deficit two. -/
def topTwoOffClosed (D n : Nat) : Int :=
  4 * (n : Int) * ((n : Int) + 1) *
    ((D : Int) - (2 * (n : Int) * ((n : Int) + 1) - 1)) *
    ((D : Int) - (2 * (n : Int) * ((n : Int) + 1) - 1) - 1)

/-- Closed polynomial recurrence for the deficit-two reverse tail. -/
def reverseTopTwoClosed (D n : Nat) : Nat → Int
  | 0 => topTwoDiagClosed D n
  | c + 1 =>
      topTwoDiagClosed D n - topTwoOffClosed D n +
        reverseTopTwoClosed D (n + 1) c

/-- Exact arbitrary-tail deficit-two formula, doubled to avoid division. -/
theorem two_mul_reverseTailCoeff_top_two (D n c : Nat) (hnpos : 0 < n)
    (hD : 2 * (n + c) * (n + c) + 1 ≤ D) :
    2 * reverseTailCoeff D n (D - 2) c =
      2 * reverseTopTwoClosed D n c := by
  induction c generalizing n with
  | zero =>
      simp only [reverseTailCoeff, reverseTopTwoClosed, topTwoDiagClosed]
      exact two_mul_diagCoeff_top_two hnpos (by simpa using hD)
  | succ c ih =>
      simp only [reverseTailCoeff, reverseTopTwoClosed]
      have hnle : n ≤ n + (c + 1) := by omega
      have hn1le : n + 1 ≤ n + (c + 1) := by omega
      have hsquare : n * n ≤ (n + (c + 1)) * (n + (c + 1)) :=
        Nat.mul_le_mul hnle hnle
      have hrect : n * (n + 1) ≤ (n + (c + 1)) * (n + (c + 1)) :=
        Nat.mul_le_mul hnle hn1le
      have hn : 2 * n * n + 1 ≤ D := by
        simp only [Nat.mul_assoc] at hD ⊢
        omega
      have hoff : 2 * n * (n + 1) - 1 ≤ D := by
        simp only [Nat.mul_assoc] at hD ⊢
        omega
      rw [Int.mul_add]
      rw [two_mul_topTwo_cell_drift D n hnpos hn hoff]
      rw [ih (n + 1) (by omega) (by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hD)]
      rw [← Int.mul_add]
      unfold topTwoDiagClosed topTwoOffClosed
      rfl

/-- Append one terminal cell to the closed deficit-two reverse tail. -/
theorem reverseTopTwoClosed_append (D n c : Nat) :
    reverseTopTwoClosed D n (c + 1) =
      reverseTopTwoClosed D n c - topTwoOffClosed D (n + c) +
        topTwoDiagClosed D (n + c + 1) := by
  induction c generalizing n with
  | zero =>
      simp [reverseTopTwoClosed]
  | succ c ih =>
      change
        topTwoDiagClosed D n - topTwoOffClosed D n +
            reverseTopTwoClosed D (n + 1) (c + 1) =
          (topTwoDiagClosed D n - topTwoOffClosed D n +
            reverseTopTwoClosed D (n + 1) c) -
            topTwoOffClosed D (n + (c + 1)) +
              topTwoDiagClosed D (n + (c + 1) + 1)
      rw [ih (n + 1)]
      simp only [Int.sub_eq_add_neg]
      ac_rfl

/-! Canonical power normalization for the start-one collapse. -/

private def iPow (x : Int) : Nat → Int
  | 0 => 1
  | k + 1 => x * iPow x k

private theorem iPow_one (x : Int) : iPow x 1 = x := by simp [iPow]

private theorem x_mul_iPow (x k : Int) (j : Nat) :
    x * (k * iPow x j) = k * iPow x (j + 1) := by
  change x * (k * iPow x j) = k * (x * iPow x j)
  ac_rfl

private theorem iPow_mul (x : Int) : ∀ a b : Nat,
    iPow x a*iPow x b=iPow x (a+b)
  | 0, b => by simp [iPow]
  | a+1, b => by
      change (x*iPow x a)*iPow x b=iPow x (a+1+b)
      rw [show a+1+b=(a+b)+1 by omega]
      change (x*iPow x a)*iPow x b=x*iPow x (a+b)
      rw [Int.mul_assoc,iPow_mul x a b]

private theorem iPow_add_one_two (x : Int) :
    iPow (x + 1) 2 = iPow x 2 + 2 * iPow x 1 + 1 := by
  change (x + 1) * iPow (x + 1) 1 = x * iPow x 1 + 2 * iPow x 1 + 1
  rw [iPow_one]
  simp only [Int.mul_add, Int.add_mul]
  rw [iPow_one]
  omega

private theorem iPow_add_one_three (x : Int) :
    iPow (x + 1) 3 = iPow x 3 + 3 * iPow x 2 + 3 * iPow x 1 + 1 := by
  change (x + 1) * iPow (x + 1) 2 =
    x * iPow x 2 + 3 * iPow x 2 + 3 * iPow x 1 + 1
  rw [iPow_add_one_two]
  simp only [Int.mul_add, Int.add_mul]
  rw [x_mul_iPow x 2 1, iPow_one]
  rw [show 1 + 1 = 2 by rfl]
  omega

private theorem iPow_add_one_four (x : Int) :
    iPow (x + 1) 4 = iPow x 4 + 4 * iPow x 3 + 6 * iPow x 2 +
      4 * iPow x 1 + 1 := by
  change (x + 1) * iPow (x + 1) 3 =
    x * iPow x 3 + 4 * iPow x 3 + 6 * iPow x 2 + 4 * iPow x 1 + 1
  rw [iPow_add_one_three]
  simp only [Int.mul_add, Int.add_mul]
  rw [x_mul_iPow x 3 2, x_mul_iPow x 3 1, iPow_one]
  rw [show 2 + 1 = 3 by rfl, show 1 + 1 = 2 by rfl]
  omega

private theorem iPow_add_one_five (x : Int) :
    iPow (x + 1) 5 = iPow x 5 + 5 * iPow x 4 + 10 * iPow x 3 +
      10 * iPow x 2 + 5 * iPow x 1 + 1 := by
  change (x + 1) * iPow (x + 1) 4 =
    x * iPow x 4 + 5 * iPow x 4 + 10 * iPow x 3 + 10 * iPow x 2 +
      5 * iPow x 1 + 1
  rw [iPow_add_one_four]
  simp only [Int.mul_add, Int.add_mul]
  rw [x_mul_iPow x 4 3, x_mul_iPow x 6 2, x_mul_iPow x 4 1, iPow_one]
  rw [show 3 + 1 = 4 by rfl, show 2 + 1 = 3 by rfl,
    show 1 + 1 = 2 by rfl]
  omega

private theorem iPow_add_one_six (x : Int) :
    iPow (x + 1) 6 = iPow x 6 + 6 * iPow x 5 + 15 * iPow x 4 +
      20 * iPow x 3 + 15 * iPow x 2 + 6 * iPow x 1 + 1 := by
  change (x + 1) * iPow (x + 1) 5 =
    x * iPow x 5 + 6 * iPow x 5 + 15 * iPow x 4 + 20 * iPow x 3 +
      15 * iPow x 2 + 6 * iPow x 1 + 1
  rw [iPow_add_one_five]
  simp only [Int.mul_add, Int.add_mul]
  rw [x_mul_iPow x 5 4, x_mul_iPow x 10 3, x_mul_iPow x 10 2,
    x_mul_iPow x 5 1, iPow_one]
  rw [show 4 + 1 = 5 by rfl, show 3 + 1 = 4 by rfl,
    show 2 + 1 = 3 by rfl, show 1 + 1 = 2 by rfl]
  omega

private theorem iPow_add_one_seven (x : Int) :
    iPow (x+1) 7=iPow x 7+7*iPow x 6+21*iPow x 5+35*iPow x 4+
      35*iPow x 3+21*iPow x 2+7*iPow x 1+1 := by
  change (x+1)*iPow (x+1) 6 =
    x*iPow x 6+7*iPow x 6+21*iPow x 5+35*iPow x 4+35*iPow x 3+
      21*iPow x 2+7*iPow x 1+1
  rw [iPow_add_one_six]
  simp only [Int.mul_add,Int.add_mul]
  rw [x_mul_iPow x 6 5,x_mul_iPow x 15 4,x_mul_iPow x 20 3,
    x_mul_iPow x 15 2,x_mul_iPow x 6 1,iPow_one]
  rw [show 5+1=6 by rfl,show 4+1=5 by rfl,show 3+1=4 by rfl,
    show 2+1=3 by rfl,show 1+1=2 by rfl]
  omega

private theorem iPow_add_one_eight (x : Int) :
    iPow (x+1) 8=iPow x 8+8*iPow x 7+28*iPow x 6+56*iPow x 5+
      70*iPow x 4+56*iPow x 3+28*iPow x 2+8*iPow x 1+1 := by
  change (x+1)*iPow (x+1) 7 =
    x*iPow x 7+8*iPow x 7+28*iPow x 6+56*iPow x 5+70*iPow x 4+
      56*iPow x 3+28*iPow x 2+8*iPow x 1+1
  rw [iPow_add_one_seven]
  simp only [Int.mul_add,Int.add_mul]
  rw [x_mul_iPow x 7 6,x_mul_iPow x 21 5,x_mul_iPow x 35 4,
    x_mul_iPow x 35 3,x_mul_iPow x 21 2,x_mul_iPow x 7 1,iPow_one]
  rw [show 6+1=7 by rfl,show 5+1=6 by rfl,show 4+1=5 by rfl,
    show 3+1=4 by rfl,show 2+1=3 by rfl,show 1+1=2 by rfl]
  omega

/-- Start-one doubled deficit-two polynomial in canonical powers. -/
def startTwoPoly (d x : Int) : Int :=
  2*d*d*iPow x 2 + 2*d*d*x - 8*d*iPow x 4 - 12*d*iPow x 3 + 4*d*x +
    8*iPow x 6 + 16*iPow x 5 - 10*iPow x 3 + iPow x 2 + 3*x

private def startTwoDelta (d x : Int) : Int :=
  4*d*d*x + 4*d*d - 32*d*iPow x 3 - 84*d*iPow x 2 - 68*d*x - 16*d +
    48*iPow x 5 + 200*iPow x 4 + 320*iPow x 3 + 250*iPow x 2 + 100*x + 18

/-- The proposed start-one closed polynomial has the exact terminal-step
finite difference. -/
theorem startTwoPoly_step (d x : Int) :
    startTwoPoly d (x + 1) = startTwoPoly d x + startTwoDelta d x := by
  unfold startTwoPoly startTwoDelta
  rw [iPow_add_one_two, iPow_add_one_three, iPow_add_one_four,
    iPow_add_one_five, iPow_add_one_six]
  simp only [Int.mul_add]
  rw [iPow_one]
  have hg : 2*d*d*(2*x)=4*d*d*x := by
    rw [show (4:Int)=2*2 by decide]; ac_rfl
  have hh : 4*d*d=2*(2*d*d) := by
    rw [show (4:Int)=2*2 by decide]; ac_rfl
  have hi : 8*d*(4*iPow x 3)=32*d*iPow x 3 := by
    rw [show (32:Int)=8*4 by decide]; ac_rfl
  have he : 8*d*(6*iPow x 2)+12*d*(3*iPow x 2)=84*d*iPow x 2 := by
    rw [show (84:Int)=8*6+12*3 by decide]
    simp only [Int.add_mul]; ac_rfl
  have hf : 8*d*(4*x)+12*d*(3*x)=68*d*x := by
    rw [show (68:Int)=8*4+12*3 by decide]
    simp only [Int.add_mul]; ac_rfl
  omega

private def startThreeA (x : Int) : Int := iPow x 2+x
private def startThreeB (x : Int) : Int :=
  -120*iPow x 4-180*iPow x 3-30*iPow x 2+30*x
private def startThreeC (x : Int) : Int :=
  240*iPow x 6+480*iPow x 5+120*iPow x 4-120*iPow x 3+
    40*iPow x 2+40*x
private def startThreeE (x : Int) : Int :=
  -160*iPow x 8-400*iPow x 7-120*iPow x 6+216*iPow x 5-
  80*iPow x 4-210*iPow x 3-15*iPow x 2+19*x

/-- Five times the cleared start-one third-deficit polynomial.  Since the
cleared suffix itself is six times the coefficient, this normalization gives
the division-free factor `30*b₃`. -/
def startThreePoly5 (d x : Int) : Int :=
  20*d*d*d*startThreeA x+d*d*startThreeB x+d*startThreeC x+startThreeE x

private def startThreeBDelta (x : Int) : Int :=
  -480*iPow x 3-1260*iPow x 2-1080*x-300
private def startThreeCDelta (x : Int) : Int :=
  1440*iPow x 5+6000*iPow x 4+10080*iPow x 3+
    8760*iPow x 2+4040*x+800
private def startThreeEDelta (x : Int) : Int :=
  -1280*iPow x 7-7280*iPow x 6-18080*iPow x 5-25920*iPow x 4-
    23520*iPow x 3-13630*iPow x 2-4700*x-750

private def startThreeDelta5 (d x : Int) : Int :=
  40*d*d*d*x+40*d*d*d+d*d*startThreeBDelta x+
    d*startThreeCDelta x+startThreeEDelta x

private theorem startThreeA_step (x : Int) :
    startThreeA (x+1)=startThreeA x+2*x+2 := by
  unfold startThreeA
  rw [iPow_add_one_two,iPow_one]
  omega

private theorem startThreeB_step (x : Int) :
    startThreeB (x+1)=startThreeB x+startThreeBDelta x := by
  unfold startThreeB startThreeBDelta
  rw [iPow_add_one_two,iPow_add_one_three,iPow_add_one_four,iPow_one]
  simp only [Int.mul_add]
  omega

private theorem startThreeC_step (x : Int) :
    startThreeC (x+1)=startThreeC x+startThreeCDelta x := by
  unfold startThreeC startThreeCDelta
  rw [iPow_add_one_two,iPow_add_one_three,iPow_add_one_four,
    iPow_add_one_five,iPow_add_one_six,iPow_one]
  simp only [Int.mul_add]
  omega

private theorem startThreeE_step (x : Int) :
    startThreeE (x+1)=startThreeE x+startThreeEDelta x := by
  unfold startThreeE startThreeEDelta
  rw [iPow_add_one_two,iPow_add_one_three,iPow_add_one_four,
    iPow_add_one_five,iPow_add_one_six,iPow_add_one_seven,
    iPow_add_one_eight,iPow_one]
  simp only [Int.mul_add]
  omega

/-- Exact finite difference of the start-one third-deficit polynomial. -/
theorem startThreePoly5_step (d x : Int) :
    startThreePoly5 d (x+1)=startThreePoly5 d x+startThreeDelta5 d x := by
  unfold startThreePoly5 startThreeDelta5
  rw [startThreeA_step,startThreeB_step,startThreeC_step,startThreeE_step]
  simp only [Int.mul_add]
  have hx : 20*d*d*d*(2*x)=40*d*d*d*x := by
    rw [show (40:Int)=20*2 by decide]
    ac_rfl
  have h1 : 20*d*d*d*2=40*d*d*d := by
    rw [show (40:Int)=20*2 by decide]
    ac_rfl
  omega

private def topThreeDiagInt (d x : Int) : Int :=
  let z:=d-2*x*x+2
  x*x*(intFallThree z+3*intFallThree (z-1)+
    3*intFallThree (z-2)+intFallThree (z-3))

private def topThreeOffInt (d x : Int) : Int :=
  8*x*(x+1)*intFallThree (d-2*x*(x+1)+1)

private theorem intFallThree_expanded (z : Int) :
    intFallThree z=iPow z 3-3*iPow z 2+2*z := by
  unfold intFallThree
  simp only [Int.sub_mul,Int.mul_sub,Int.add_mul,Int.mul_add,Int.mul_one,
    Int.mul_assoc]
  have hz2 : z*2=2*z := by ac_rfl
  have hsq : z*z=iPow z 2 := by dsimp [iPow]; rw [Int.mul_one]
  have hcu : z*(z*z)=iPow z 3 := by dsimp [iPow]; ac_rfl
  have h2z : z*(2*z)=2*iPow z 2 := by dsimp [iPow]; ac_rfl
  rw [hcu,hsq,hz2,h2z]
  omega

private theorem intFallThree_shift_one (z : Int) :
    intFallThree (z-1)=iPow z 3-6*iPow z 2+11*z-6 := by
  unfold intFallThree
  simp only [Int.sub_mul,Int.mul_sub,Int.add_mul,Int.mul_add,Int.mul_one,
    Int.mul_assoc]
  have hz2 : z*2=2*z := by ac_rfl
  have hsq : z*z=iPow z 2 := by dsimp [iPow]; rw [Int.mul_one]
  have hcu : z*(z*z)=iPow z 3 := by dsimp [iPow]; ac_rfl
  have h2z : z*(2*z)=2*iPow z 2 := by dsimp [iPow]; ac_rfl
  rw [hcu,hsq,hz2,h2z]
  simp only [Int.one_mul]
  omega

private theorem intFallThree_shift_two (z : Int) :
    intFallThree (z-2)=iPow z 3-9*iPow z 2+26*z-24 := by
  unfold intFallThree
  simp only [Int.sub_mul,Int.mul_sub,Int.add_mul,Int.mul_add,Int.mul_one,
    Int.mul_assoc]
  have hz2 : z*2=2*z := by ac_rfl
  have hsq : z*z=iPow z 2 := by dsimp [iPow]; rw [Int.mul_one]
  have hcu : z*(z*z)=iPow z 3 := by dsimp [iPow]; ac_rfl
  have h2z : z*(2*z)=2*iPow z 2 := by dsimp [iPow]; ac_rfl
  rw [hcu,hsq,hz2,h2z]
  omega

private theorem intFallThree_shift_three (z : Int) :
    intFallThree (z-3)=iPow z 3-12*iPow z 2+47*z-60 := by
  unfold intFallThree
  simp only [Int.sub_mul,Int.mul_sub,Int.add_mul,Int.mul_add,Int.mul_one,
    Int.mul_assoc]
  have hz2 : z*2=2*z := by ac_rfl
  have hz3 : z*3=3*z := by ac_rfl
  have hsq : z*z=iPow z 2 := by dsimp [iPow]; rw [Int.mul_one]
  have hcu : z*(z*z)=iPow z 3 := by dsimp [iPow]; ac_rfl
  have h2z : z*(2*z)=2*iPow z 2 := by dsimp [iPow]; ac_rfl
  have h3z : z*(3*z)=3*iPow z 2 := by dsimp [iPow]; ac_rfl
  rw [hcu,hsq,hz2,hz3,h2z,h3z]
  omega

private theorem intFallThree_binomial_three (z : Int) :
    intFallThree z+3*intFallThree (z-1)+3*intFallThree (z-2)+
        intFallThree (z-3)=8*iPow z 3-60*iPow z 2+160*z-150 := by
  rw [intFallThree_expanded,intFallThree_shift_one,
    intFallThree_shift_two,intFallThree_shift_three]
  omega

private theorem iPow_sub_twice_add_two_square (d A : Int) :
    iPow (d-2*A+2) 2=iPow d 2-4*d*A+4*d+4*iPow A 2-8*A+4 := by
  dsimp [iPow]
  simp only [Int.sub_mul,Int.mul_sub,Int.add_mul,Int.mul_add,Int.mul_one]
  have hdd : d*d=iPow d 2 := by dsimp [iPow]; rw [Int.mul_one]
  have hda : d*(2*A)=2*d*A := by ac_rfl
  have had : (2*A)*d=2*d*A := by ac_rfl
  have haa : (2*A)*(2*A)=4*iPow A 2 := by dsimp [iPow]; ac_rfl
  have hd2 : d*2=2*d := by ac_rfl
  have ha2 : (2*A)*2=4*A := by ac_rfl
  have h2a : 2*(2*A)=4*A := by ac_rfl
  have h22 : (2:Int)*2=4 := by decide
  rw [hdd,hda,had,haa,hd2,ha2,h2a,h22]
  have h2ad : 2*A*d=2*(d*A) := by ac_rfl
  have h4da : 4*d*A=4*(d*A) := by ac_rfl
  have hAA : A*A=iPow A 2 := by dsimp [iPow]; rw [Int.mul_one]
  simp only [h2ad,h4da,hAA]
  omega

private theorem iPow_sub_twice_add_two_cube (d A : Int) :
    iPow (d-2*A+2) 3=
      iPow d 3-6*iPow d 2*A+6*iPow d 2+12*d*iPow A 2-
        24*d*A+12*d-8*iPow A 3+24*iPow A 2-24*A+8 := by
  change (d-2*A+2)*iPow (d-2*A+2) 2=_
  rw [iPow_sub_twice_add_two_square]
  simp only [Int.sub_mul,Int.mul_sub,Int.add_mul,Int.mul_add,Int.mul_one,
    Int.one_mul,Int.mul_assoc]
  have hi : d*iPow d 2=iPow d 3 := by dsimp [iPow]
  have hj : A*iPow d 2=iPow d 2*A := by ac_rfl
  have hk : d*(4*(d*A))=4*iPow d 2*A := by dsimp [iPow]; ac_rfl
  have hl : A*(4*(d*A))=4*d*iPow A 2 := by dsimp [iPow]; ac_rfl
  have hm : d*(4*d)=4*iPow d 2 := by dsimp [iPow]; ac_rfl
  have hn : A*(4*d)=4*d*A := by ac_rfl
  have ho : d*(4*iPow A 2)=4*d*iPow A 2 := by ac_rfl
  have hp : A*(4*iPow A 2)=4*iPow A 3 := by dsimp [iPow]; ac_rfl
  have hq : d*(8*A)=8*d*A := by ac_rfl
  have hr : A*(8*A)=8*iPow A 2 := by dsimp [iPow]; ac_rfl
  rw [hi,hj,hk,hl,hm,hn,ho,hp,hq,hr]
  have hk' : 4*iPow d 2*A=4*(iPow d 2*A) := by ac_rfl
  have h4da : 4*d*A=4*(d*A) := by ac_rfl
  have h8da : 8*d*A=8*(d*A) := by ac_rfl
  have h24da : 24*d*A=24*(d*A) := by ac_rfl
  have h4dA2 : 4*d*iPow A 2=4*(d*iPow A 2) := by ac_rfl
  have h12dA2 : 12*d*iPow A 2=12*(d*iPow A 2) := by ac_rfl
  simp only [hk',h4da,h8da,h24da,h4dA2,h12dA2]
  omega

private theorem topThreeDiagInt_generic (d A : Int) :
    A*(8*iPow (d-2*A+2) 3-60*iPow (d-2*A+2) 2+160*(d-2*A+2)-150)=
      8*iPow d 3*A+iPow d 2*(-48*iPow A 2-12*A)+
        d*(96*iPow A 3+48*iPow A 2+16*A)-
          64*iPow A 4-48*iPow A 3-32*iPow A 2-6*A := by
  rw [iPow_sub_twice_add_two_cube,iPow_sub_twice_add_two_square]
  simp only [Int.sub_mul,Int.mul_sub,Int.add_mul,Int.mul_add,Int.mul_one,
    Int.one_mul,Int.mul_assoc]
  let b1:=iPow d 3*A
  let b2:=iPow d 2*iPow A 2
  let b3:=iPow d 2*A
  let b4:=d*iPow A 3
  let b5:=d*iPow A 2
  let b6:=d*A
  let b7:=iPow A 4
  let b8:=iPow A 3
  let b9:=iPow A 2
  have hb1 : iPow d 3*A=b1 := by rfl
  have hb2 : iPow d 2*iPow A 2=b2 := by rfl
  have hb3 : iPow d 2*A=b3 := by rfl
  have hb4 : d*iPow A 3=b4 := by rfl
  have hb5 : d*iPow A 2=b5 := by rfl
  have hb6 : d*A=b6 := by rfl
  have hb7 : iPow A 4=b7 := by rfl
  have hb8 : iPow A 3=b8 := by rfl
  have hb9 : iPow A 2=b9 := by rfl
  have hk : A*(8*iPow d 3)=8*b1 := by dsimp [b1]; ac_rfl
  have hl : A*(8*(6*(iPow d 2*A)))=48*b2 := by
    dsimp [b2,iPow]; rw [show (48:Int)=8*6 by decide]; ac_rfl
  have hm : A*(8*(6*iPow d 2))=48*b3 := by
    dsimp [b3]; rw [show (48:Int)=8*6 by decide]; ac_rfl
  have hn : A*(8*(12*(d*iPow A 2)))=96*b4 := by
    dsimp [b4,iPow]; rw [show (96:Int)=8*12 by decide]; ac_rfl
  have ho : A*(8*(24*(d*A)))=192*b5 := by
    dsimp [b5,iPow]; rw [show (192:Int)=8*24 by decide]; ac_rfl
  have hp : A*(8*(12*d))=96*b6 := by
    dsimp [b6]; rw [show (96:Int)=8*12 by decide]; ac_rfl
  have hq : A*(8*(8*iPow A 3))=64*b7 := by
    dsimp [b7,iPow]; rw [show (64:Int)=8*8 by decide]; ac_rfl
  have hr : A*(8*(24*iPow A 2))=192*b8 := by
    dsimp [b8,iPow]; rw [show (192:Int)=8*24 by decide]; ac_rfl
  have hs : A*(8*(24*A))=192*b9 := by
    dsimp [b9,iPow]; rw [show (192:Int)=8*24 by decide]; ac_rfl
  have ht : A*(60*iPow d 2)=60*b3 := by dsimp [b3]; ac_rfl
  have hu : A*(60*(4*(d*A)))=240*b5 := by
    dsimp [b5,iPow]; rw [show (240:Int)=60*4 by decide]; ac_rfl
  have hv : A*(60*(4*d))=240*b6 := by
    dsimp [b6]; rw [show (240:Int)=60*4 by decide]; ac_rfl
  have hw : A*(60*(4*iPow A 2))=240*b8 := by
    dsimp [b8,iPow]; rw [show (240:Int)=60*4 by decide]; ac_rfl
  have hx : A*(60*(8*A))=480*b9 := by
    dsimp [b9,iPow]; rw [show (480:Int)=60*8 by decide]; ac_rfl
  have hy : A*(160*d)=160*b6 := by dsimp [b6]; ac_rfl
  have hz : A*(160*(2*A))=320*b9 := by
    dsimp [b9,iPow]; rw [show (320:Int)=160*2 by decide]; ac_rfl
  rw [hk,hl,hm,hn,ho,hp,hq,hr,hs,ht,hu,hv,hw,hx,hy,hz]
  have hneg48 : iPow d 2*(-48*iPow A 2)=-48*b2 := by
    dsimp [b2]; ac_rfl
  have h12 : iPow d 2*(12*A)=12*b3 := by dsimp [b3]; ac_rfl
  have h96 : d*(96*iPow A 3)=96*b4 := by dsimp [b4]; ac_rfl
  have h48 : d*(48*iPow A 2)=48*b5 := by dsimp [b5]; ac_rfl
  have h16 : d*(16*A)=16*b6 := by dsimp [b6]; ac_rfl
  rw [hneg48,h12,h96,h48,h16]
  simp only [hb1,hb2,hb3,hb4,hb5,hb6,hb7,hb8,hb9]
  omega

private theorem iPow_sub_twice_add_one_square (d A : Int) :
    iPow (d-2*A+1) 2=iPow d 2-4*d*A+2*d+4*iPow A 2-4*A+1 := by
  dsimp [iPow]
  simp only [Int.sub_mul,Int.mul_sub,Int.add_mul,Int.mul_add,Int.mul_one]
  have hdd : d*d=iPow d 2 := by dsimp [iPow]; rw [Int.mul_one]
  have hda : d*(2*A)=2*d*A := by ac_rfl
  have had : (2*A)*d=2*d*A := by ac_rfl
  have haa : (2*A)*(2*A)=4*iPow A 2 := by dsimp [iPow]; ac_rfl
  rw [hdd,hda,had,haa]
  have h2ad : 2*A*d=2*(d*A) := by ac_rfl
  have h4da : 4*d*A=4*(d*A) := by ac_rfl
  have hAA : A*A=iPow A 2 := by dsimp [iPow]; rw [Int.mul_one]
  simp only [h2ad,h4da,hAA,Int.one_mul]
  omega

private theorem iPow_sub_twice_add_one_cube (d A : Int) :
    iPow (d-2*A+1) 3=
      iPow d 3-6*iPow d 2*A+3*iPow d 2+12*d*iPow A 2-
        12*d*A+3*d-8*iPow A 3+12*iPow A 2-6*A+1 := by
  change (d-2*A+1)*iPow (d-2*A+1) 2=_
  rw [iPow_sub_twice_add_one_square]
  simp only [Int.sub_mul,Int.mul_sub,Int.add_mul,Int.mul_add,Int.mul_one,
    Int.one_mul,Int.mul_assoc]
  have hi : d*iPow d 2=iPow d 3 := by dsimp [iPow]
  have hj : A*iPow d 2=iPow d 2*A := by ac_rfl
  have hk : d*(4*(d*A))=4*iPow d 2*A := by dsimp [iPow]; ac_rfl
  have hl : A*(4*(d*A))=4*d*iPow A 2 := by dsimp [iPow]; ac_rfl
  have hm : d*(2*d)=2*iPow d 2 := by dsimp [iPow]; ac_rfl
  have hn : A*(2*d)=2*d*A := by ac_rfl
  have ho : d*(4*iPow A 2)=4*d*iPow A 2 := by ac_rfl
  have hp : A*(4*iPow A 2)=4*iPow A 3 := by dsimp [iPow]; ac_rfl
  have hq : d*(4*A)=4*d*A := by ac_rfl
  have hr : A*(4*A)=4*iPow A 2 := by dsimp [iPow]; ac_rfl
  rw [hi,hj,hk,hl,hm,hn,ho,hp,hq,hr]
  have hk' : 4*iPow d 2*A=4*(iPow d 2*A) := by ac_rfl
  have h2d2A : 2*iPow d 2*A=2*(iPow d 2*A) := by ac_rfl
  have h2da : 2*d*A=2*(d*A) := by ac_rfl
  have h4da : 4*d*A=4*(d*A) := by ac_rfl
  have h12da : 12*d*A=12*(d*A) := by ac_rfl
  have h4dA2 : 4*d*iPow A 2=4*(d*iPow A 2) := by ac_rfl
  have h12dA2 : 12*d*iPow A 2=12*(d*iPow A 2) := by ac_rfl
  simp only [hk',h2d2A,h2da,h4da,h12da,h4dA2,h12dA2]
  omega

private theorem topThreeOffInt_generic (d A : Int) :
    8*A*intFallThree (d-2*A+1)=
      8*iPow d 3*A-48*iPow d 2*iPow A 2+
        d*(96*iPow A 3-8*A)-64*iPow A 4+16*iPow A 2 := by
  rw [intFallThree_expanded,iPow_sub_twice_add_one_cube,
    iPow_sub_twice_add_one_square]
  simp only [Int.sub_mul,Int.mul_sub,Int.add_mul,Int.mul_add,Int.mul_one,
    Int.one_mul,Int.mul_assoc]
  let b1:=iPow d 3*A
  let b2:=iPow d 2*iPow A 2
  let b3:=d*iPow A 3
  let b4:=d*A
  let b5:=iPow A 4
  let b6:=iPow A 2
  let b7:=d*iPow A 2
  let b8:=iPow A 3
  have hh : A*iPow d 3=b1 := by dsimp [b1]; ac_rfl
  have hi : A*(6*(iPow d 2*A))=6*b2 := by
    dsimp [b2,iPow]; ac_rfl
  have hj : A*(12*(d*iPow A 2))=12*b3 := by
    dsimp [b3,iPow]; ac_rfl
  have hk : A*(12*(d*A))=12*b7 := by dsimp [b7,iPow]; ac_rfl
  have hl : A*(3*d)=3*b4 := by dsimp [b4]; ac_rfl
  have hm : A*(8*iPow A 3)=8*b5 := by dsimp [b5,iPow]; ac_rfl
  have hn : A*(12*iPow A 2)=12*b8 := by dsimp [b8,iPow]; ac_rfl
  have ho : A*(6*A)=6*b6 := by dsimp [b6,iPow]; ac_rfl
  have hp : A*(3*(4*(d*A)))=12*b7 := by
    dsimp [b7,iPow]; rw [show (12:Int)=3*4 by decide]; ac_rfl
  have hq : A*(3*(2*d))=6*b4 := by
    dsimp [b4]; rw [show (6:Int)=3*2 by decide]; ac_rfl
  have hr : A*(3*(4*iPow A 2))=12*b8 := by
    dsimp [b8,iPow]; rw [show (12:Int)=3*4 by decide]; ac_rfl
  have hs : A*(3*(4*A))=12*b6 := by
    dsimp [b6,iPow]; rw [show (12:Int)=3*4 by decide]; ac_rfl
  have ht : A*(2*d)=2*b4 := by dsimp [b4]; ac_rfl
  have hu : A*(2*(2*A))=4*b6 := by
    dsimp [b6,iPow]; rw [show (4:Int)=2*2 by decide]; ac_rfl
  rw [hh,hi,hj,hk,hl,hm,hn,ho,hp,hq,hr,hs,ht,hu]
  have hc : d*(96*iPow A 3)=96*b3 := by dsimp [b3]; ac_rfl
  have he : d*(8*A)=8*b4 := by dsimp [b4]; ac_rfl
  have hb1 : iPow d 3*A=b1 := by rfl
  have hb2 : iPow d 2*iPow A 2=b2 := by rfl
  have hb5 : 64*iPow A 4=64*b5 := by rfl
  have hb6 : 16*iPow A 2=16*b6 := by rfl
  rw [hc,he]
  rw [hb1,hb2,hb5,hb6]
  omega

private theorem topThreeDiagInt_expanded (d y : Int) :
    topThreeDiagInt d y=
      8*iPow d 3*iPow y 2+
      iPow d 2*(-48*iPow y 4-12*iPow y 2)+
      d*(96*iPow y 6+48*iPow y 4+16*iPow y 2)-
      64*iPow y 8-48*iPow y 6-32*iPow y 4-6*iPow y 2 := by
  unfold topThreeDiagInt
  dsimp
  rw [intFallThree_binomial_three]
  have hy : y*y=iPow y 2 := by dsimp [iPow]; rw [Int.mul_one]
  simp only [hy]
  have h2y : 2*y*y=2*iPow y 2 := by
    rw [show 2*y*y=2*(y*y) by ac_rfl,hy]
  rw [h2y]
  rw [topThreeDiagInt_generic]
  have h2 : iPow (iPow y 2) 2=iPow y 4 := by dsimp [iPow]; ac_rfl
  have h3 : iPow (iPow y 2) 3=iPow y 6 := by dsimp [iPow]; ac_rfl
  have h4 : iPow (iPow y 2) 4=iPow y 8 := by dsimp [iPow]; ac_rfl
  rw [h2,h3,h4]

private theorem topThreeOffInt_expanded_A (d x : Int) :
    let A:=x*(x+1)
    topThreeOffInt d x=
      8*iPow d 3*A-48*iPow d 2*iPow A 2+
      d*(96*iPow A 3-8*A)-64*iPow A 4+16*iPow A 2 := by
  dsimp
  unfold topThreeOffInt
  let A:=x*(x+1)
  have h8 : 8*x*(x+1)=8*A := by dsimp [A]; ac_rfl
  have h2 : 2*x*(x+1)=2*A := by dsimp [A]; ac_rfl
  rw [h8,h2]
  exact topThreeOffInt_generic d A

private theorem crossPow_two (x : Int) :
    iPow (x*(x+1)) 2=iPow x 4+2*iPow x 3+iPow x 2 := by
  dsimp [iPow]
  simp only [Int.mul_add,Int.add_mul,Int.mul_one]
  have h4 : x*x*(x*x)=iPow x 4 := by dsimp [iPow]; ac_rfl
  have h3a : x*x*x=iPow x 3 := by dsimp [iPow]; ac_rfl
  have h3b : x*(x*x)=iPow x 3 := by dsimp [iPow]; ac_rfl
  have h2 : x*x=iPow x 2 := by dsimp [iPow]; rw [Int.mul_one]
  have h4c : x*iPow x 3=iPow x 4 := by dsimp [iPow]
  rw [h4,h3a,h3b,h2,h4c]
  omega

private theorem crossPow_three (x : Int) :
    iPow (x*(x+1)) 3=
      iPow x 6+3*iPow x 5+3*iPow x 4+iPow x 3 := by
  change (x*(x+1))*iPow (x*(x+1)) 2=_
  rw [crossPow_two]
  simp only [Int.mul_add,Int.add_mul,Int.mul_one]
  have h6 : x*x*iPow x 4=iPow x 6 := by dsimp [iPow]; ac_rfl
  have h5a : x*x*(2*iPow x 3)=2*iPow x 5 := by dsimp [iPow]; ac_rfl
  have h4a : x*x*iPow x 2=iPow x 4 := by dsimp [iPow]; ac_rfl
  have h5b : x*iPow x 4=iPow x 5 := by dsimp [iPow]
  have h4b : x*(2*iPow x 3)=2*iPow x 4 := by dsimp [iPow]; ac_rfl
  have h3 : x*iPow x 2=iPow x 3 := by dsimp [iPow]
  rw [h6,h5a,h4a,h5b,h4b,h3]
  omega

private theorem crossPow_four (x : Int) :
    iPow (x*(x+1)) 4=
      iPow x 8+4*iPow x 7+6*iPow x 6+4*iPow x 5+iPow x 4 := by
  change (x*(x+1))*iPow (x*(x+1)) 3=_
  rw [crossPow_three]
  simp only [Int.mul_add,Int.add_mul,Int.mul_one]
  have h8 : x*x*iPow x 6=iPow x 8 := by dsimp [iPow]; ac_rfl
  have h7a : x*x*(3*iPow x 5)=3*iPow x 7 := by dsimp [iPow]; ac_rfl
  have h6a : x*x*(3*iPow x 4)=3*iPow x 6 := by dsimp [iPow]; ac_rfl
  have h5a : x*x*iPow x 3=iPow x 5 := by dsimp [iPow]; ac_rfl
  have h7b : x*iPow x 6=iPow x 7 := by dsimp [iPow]
  have h6b : x*(3*iPow x 5)=3*iPow x 6 := by dsimp [iPow]; ac_rfl
  have h5b : x*(3*iPow x 4)=3*iPow x 5 := by dsimp [iPow]; ac_rfl
  have h4 : x*iPow x 3=iPow x 4 := by dsimp [iPow]
  rw [h8,h7a,h6a,h5a,h7b,h6b,h5b,h4]
  omega

private def topThreeDiagBlock3 (y : Int) : Int := 8*iPow y 2
private def topThreeDiagBlock2 (y : Int) : Int :=
  -48*iPow y 4-12*iPow y 2
private def topThreeDiagBlock1 (y : Int) : Int :=
  96*iPow y 6+48*iPow y 4+16*iPow y 2
private def topThreeDiagBlock0 (y : Int) : Int :=
  -64*iPow y 8-48*iPow y 6-32*iPow y 4-6*iPow y 2

private def topThreeOffBlock3 (x : Int) : Int := 8*(x*(x+1))
private def topThreeOffBlock2 (x : Int) : Int :=
  -48*iPow (x*(x+1)) 2
private def topThreeOffBlock1 (x : Int) : Int :=
  96*iPow (x*(x+1)) 3-8*(x*(x+1))
private def topThreeOffBlock0 (x : Int) : Int :=
  -64*iPow (x*(x+1)) 4+16*iPow (x*(x+1)) 2

private theorem topThreeBlock3_payment (x : Int) :
    5*(topThreeDiagBlock3 (x+1)-topThreeOffBlock3 x)=40*x+40 := by
  unfold topThreeDiagBlock3 topThreeOffBlock3
  rw [iPow_add_one_two,iPow_one]
  simp only [Int.mul_add,Int.add_mul,Int.mul_one]
  rw [show x*x=iPow x 2 by dsimp [iPow]; rw [Int.mul_one]]
  omega

private theorem topThreeBlock2_payment (x : Int) :
    5*(topThreeDiagBlock2 (x+1)-topThreeOffBlock2 x)=
      startThreeBDelta x := by
  unfold topThreeDiagBlock2 topThreeOffBlock2 startThreeBDelta
  rw [iPow_add_one_two,iPow_add_one_four,crossPow_two,iPow_one]
  simp only [Int.mul_add,Int.add_mul]
  omega

private theorem topThreeBlock1_payment (x : Int) :
    5*(topThreeDiagBlock1 (x+1)-topThreeOffBlock1 x)=
      startThreeCDelta x := by
  unfold topThreeDiagBlock1 topThreeOffBlock1 startThreeCDelta
  rw [iPow_add_one_two,iPow_add_one_four,iPow_add_one_six,
    crossPow_three,iPow_one]
  simp only [Int.mul_add,Int.add_mul,Int.mul_one]
  rw [show x*x=iPow x 2 by dsimp [iPow]; rw [Int.mul_one]]
  omega

private theorem topThreeBlock0_payment (x : Int) :
    5*(topThreeDiagBlock0 (x+1)-topThreeOffBlock0 x)=
      startThreeEDelta x := by
  unfold topThreeDiagBlock0 topThreeOffBlock0 startThreeEDelta
  rw [iPow_add_one_two,iPow_add_one_four,iPow_add_one_six,
    iPow_add_one_eight,crossPow_two,crossPow_four,iPow_one]
  simp only [Int.mul_add,Int.add_mul]
  omega

private theorem topThreeDiagInt_blocks (d y : Int) :
    topThreeDiagInt d y=
      iPow d 3*topThreeDiagBlock3 y+iPow d 2*topThreeDiagBlock2 y+
        d*topThreeDiagBlock1 y+topThreeDiagBlock0 y := by
  rw [topThreeDiagInt_expanded]
  unfold topThreeDiagBlock3 topThreeDiagBlock2 topThreeDiagBlock1
    topThreeDiagBlock0
  have h3 : 8*iPow d 3*iPow y 2=iPow d 3*(8*iPow y 2) := by ac_rfl
  rw [h3]
  omega

private theorem topThreeOffInt_blocks (d x : Int) :
    topThreeOffInt d x=
      iPow d 3*topThreeOffBlock3 x+iPow d 2*topThreeOffBlock2 x+
        d*topThreeOffBlock1 x+topThreeOffBlock0 x := by
  rw [topThreeOffInt_expanded_A]
  unfold topThreeOffBlock3 topThreeOffBlock2 topThreeOffBlock1
    topThreeOffBlock0
  have h3 : 8*iPow d 3*(x*(x+1))=iPow d 3*(8*(x*(x+1))) := by ac_rfl
  have h2 : -48*iPow d 2*iPow (x*(x+1)) 2=
      iPow d 2*(-48*iPow (x*(x+1)) 2) := by ac_rfl
  rw [h3]
  have h2pos : 48*iPow d 2*iPow (x*(x+1)) 2=
      -(iPow d 2*(-48*iPow (x*(x+1)) 2)) := by
    rw [show (-48:Int)=-(48:Int) by decide]
    rw [Int.neg_mul,Int.mul_neg,Int.neg_neg]
    ac_rfl
  rw [h2pos]
  omega

private theorem fourBlock_payment (q3 q2 q1 a3 a2 a1 a0 b3 b2 b1 b0 : Int) :
    5*((q3*a3+q2*a2+q1*a1+a0)-(q3*b3+q2*b2+q1*b1+b0))=
      q3*(5*(a3-b3))+q2*(5*(a2-b2))+q1*(5*(a1-b1))+5*(a0-b0) := by
  simp only [Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul,
    Int.sub_eq_add_neg,Int.mul_neg,Int.neg_mul]
  have ha3 : q3*(5*a3)=5*(q3*a3) := by ac_rfl
  have hb3 : q3*(5*b3)=5*(q3*b3) := by ac_rfl
  have ha2 : q2*(5*a2)=5*(q2*a2) := by ac_rfl
  have hb2 : q2*(5*b2)=5*(q2*b2) := by ac_rfl
  have ha1 : q1*(5*a1)=5*(q1*a1) := by ac_rfl
  have hb1 : q1*(5*b1)=5*(q1*b1) := by ac_rfl
  rw [ha3,hb3,ha2,hb2,ha1,hb1]
  omega

private theorem five_topThree_terminal_pair_int (d x : Int) :
    5*(topThreeDiagInt d (x+1)-topThreeOffInt d x)=startThreeDelta5 d x := by
  rw [topThreeDiagInt_blocks,topThreeOffInt_blocks]
  rw [fourBlock_payment]
  rw [topThreeBlock3_payment,topThreeBlock2_payment,
    topThreeBlock1_payment,topThreeBlock0_payment]
  unfold startThreeDelta5
  have h3 : iPow d 3=d*d*d := by dsimp [iPow]; ac_rfl
  have h2 : iPow d 2=d*d := by dsimp [iPow]; rw [Int.mul_one]
  rw [h3,h2]
  simp only [Int.mul_add]
  have hx : d*d*d*(40*x)=40*d*d*d*x := by ac_rfl
  have h1 : d*d*d*40=40*d*d*d := by ac_rfl
  rw [hx,h1]

private theorem topThreeMonoClosed_cast_le {D e : Nat} (he : e≤D) :
    topThreeMonoClosed D e=intFallThree ((D:Int)-(e:Int)) := by
  by_cases h2 : e+2≤D
  · exact topThreeMonoClosed_cast h2
  · have hs : D-e≤1 := by omega
    cases hz : D-e with
    | zero =>
        unfold topThreeMonoClosed intFallThree
        simp only [hz,Int.ofNat_eq_natCast,Int.natCast_mul]
        have hde : (D:Int)-(e:Int)=0 := by
          rw [← Int.natCast_sub he,hz]
          rfl
        rw [hde]
        decide
    | succ q =>
        have hq : q=0 := by omega
        subst q
        unfold topThreeMonoClosed intFallThree
        simp only [hz,Int.ofNat_eq_natCast,Int.natCast_mul]
        have hde : (D:Int)-(e:Int)=1 := by
          rw [← Int.natCast_sub he,hz]
          rfl
        rw [hde]
        decide

private theorem topThreeDiagClosed_eq_int (D n : Nat) (hn : 0<n)
    (hD : 2*n*n+1≤D) :
    topThreeDiagClosed D n=topThreeDiagInt (D:Int) (n:Int) := by
  have h0 : 2*n*n-2≤D := by omega
  have h1 : 2*n*n-1≤D := by omega
  have h2 : 2*n*n≤D := by omega
  have hm0:=topThreeMonoClosed_cast_le h0
  have hm1:=topThreeMonoClosed_cast_le h1
  have hm2:=topThreeMonoClosed_cast_le h2
  have hm3:=topThreeMonoClosed_cast_le hD
  have hbase : 2≤2*n*n := by
    have hs : 1≤n*n := Nat.mul_le_mul hn hn
    calc
      2 = 2*1 := by rfl
      _ ≤ 2*(n*n) := Nat.mul_le_mul_left 2 hs
      _ = 2*n*n := by ac_rfl
  have he0 : ((2*n*n-2:Nat):Int)=2*(n:Int)*(n:Int)-2 := by
    rw [Int.natCast_sub hbase]
    simp only [Int.natCast_mul]
    rfl
  have he1 : ((2*n*n-1:Nat):Int)=2*(n:Int)*(n:Int)-1 := by
    rw [Int.natCast_sub (by omega : 1≤2*n*n)]
    simp only [Int.natCast_mul]
    rfl
  have he3 : ((2*n*n+1:Nat):Int)=2*(n:Int)*(n:Int)+1 := by
    simp only [Int.natCast_add,Int.natCast_mul]
    rfl
  unfold topThreeDiagClosed topThreeDiagInt
  rw [hm0,hm1,hm2,hm3]
  simp only [Int.ofNat_eq_natCast,Int.natCast_mul]
  rw [he0,he1,he3]
  have htwo : ((2:Nat):Int)=(2:Int) := rfl
  rw [htwo]
  have hz0 : (D:Int)-(2*(n:Int)*(n:Int)-2)=
      (D:Int)-2*(n:Int)*(n:Int)+2 := by omega
  have hz1 : (D:Int)-(2*(n:Int)*(n:Int)-1)=
      (D:Int)-2*(n:Int)*(n:Int)+2-1 := by omega
  have hz2 : (D:Int)-2*(n:Int)*(n:Int)=
      (D:Int)-2*(n:Int)*(n:Int)+2-2 := by omega
  have hz3 : (D:Int)-(2*(n:Int)*(n:Int)+1)=
      (D:Int)-2*(n:Int)*(n:Int)+2-3 := by omega
  rw [hz0,hz1,hz2,hz3]
  have hc2 : (D:Int)-2*(n:Int)*(n:Int)+2-2+2-2=
      (D:Int)-2*(n:Int)*(n:Int)+2-2 := by omega
  rw [hc2]
  congr 4 <;> omega

private theorem topThreeOffClosed_eq_int (D n : Nat) (hn : 0<n)
    (hD : 2*n*(n+1)-1≤D) :
    topThreeOffClosed D n=topThreeOffInt (D:Int) (n:Int) := by
  have hm:=topThreeMonoClosed_cast_le hD
  have hbase : 1≤2*n*(n+1) := by
    have hp : 1≤n*(n+1) := Nat.mul_pos hn (by omega)
    have h:=Nat.mul_le_mul_left 2 hp
    have h2 : 2≤2*n*(n+1) := by
      simpa only [Nat.mul_assoc] using h
    exact Nat.le_trans (by decide : 1≤2) h2
  have he : ((2*n*(n+1)-1:Nat):Int)=
      2*(n:Int)*((n:Int)+1)-1 := by
    rw [Int.natCast_sub hbase]
    simp only [Int.natCast_mul,Int.natCast_add]
    rfl
  unfold topThreeOffClosed topThreeOffInt
  rw [hm]
  simp only [Int.ofNat_eq_natCast,Int.natCast_mul,Int.natCast_add]
  rw [he]
  have h8 : ((8:Nat):Int)=(8:Int) := rfl
  have h1 : ((1:Nat):Int)=(1:Int) := rfl
  rw [h8,h1]
  have hz : (D:Int)-(2*(n:Int)*((n:Int)+1)-1)=
      (D:Int)-2*(n:Int)*((n:Int)+1)+1 := by omega
  rw [hz]

/-- The cleared third-deficit diagonal/off-diagonal terminal pair is exactly
the finite difference of the canonical start-one polynomial. -/
theorem topThree_terminal_pair (D m : Nat) (hm : 0<m)
    (hD : 2*(m+1)*(m+1)+1≤D) :
    5*(topThreeDiagClosed D (m+1)-topThreeOffClosed D m)=
      startThreePoly5 (D:Int) ((m:Int)+1)-startThreePoly5 (D:Int) (m:Int) := by
  have hd := topThreeDiagClosed_eq_int D (m+1) (by omega) hD
  have ho : topThreeOffClosed D m=topThreeOffInt (D:Int) (m:Int) := by
    apply topThreeOffClosed_eq_int D m hm
    have hs : m*(m+1)≤(m+1)*(m+1) := Nat.mul_le_mul_right (m+1) (by omega)
    have hs2 := Nat.mul_le_mul_left 2 hs
    have hscale : 2*m*(m+1)≤2*(m+1)*(m+1) := by
      simpa only [Nat.mul_assoc] using hs2
    have htop : 2*(m+1)*(m+1)≤D := by omega
    exact Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans hscale htop)
  rw [hd,ho]
  rw [startThreePoly5_step]
  have hp:=five_topThree_terminal_pair_int (D:Int) (m:Int)
  have hc : ((m+1:Nat):Int)=(m:Int)+1 := by
    simp only [Int.natCast_add]
    rfl
  rw [hc]
  rw [hp]
  omega

private theorem five_topThreeDiagInt_one (d : Int) :
    5*topThreeDiagInt d 1=startThreePoly5 d 1 := by
  rw [topThreeDiagInt_expanded]
  unfold startThreePoly5 startThreeA startThreeB startThreeC startThreeE
  simp [iPow]
  have hd3 : d*(d*d)=d*d*d := by ac_rfl
  rw [hd3]
  have h20 : 20*d*d*d=20*(d*d*d) := by ac_rfl
  rw [h20]
  omega

/-- Every supported start-one cleared third-deficit suffix is five times the
canonical polynomial at its terminal index. -/
theorem five_reverseTopThreeClosed_start_one (D c : Nat)
    (hD : 2*(c+1)*(c+1)+1≤D) :
    5*reverseTopThreeClosed D 1 c=
      startThreePoly5 (D:Int) ((c:Int)+1) := by
  induction c with
  | zero =>
      simp only [reverseTopThreeClosed]
      have hd:=topThreeDiagClosed_eq_int D 1 (by decide)
        (by simpa using hD)
      rw [hd]
      simp only [Int.natCast_zero,Int.natCast_one,Int.zero_add]
      rw [five_topThreeDiagInt_one]
  | succ c ih =>
      rw [reverseTopThreeClosed_append]
      have hprev : 2*(c+1)*(c+1)+1≤D := by
        have hs : (c+1)*(c+1)≤(c+1+1)*(c+1+1) :=
          Nat.mul_le_mul (by omega) (by omega)
        have hs2:=Nat.mul_le_mul_left 2 hs
        have hs2' : 2*(c+1)*(c+1)≤2*(c+1+1)*(c+1+1) := by
          simpa only [Nat.mul_assoc] using hs2
        omega
      rw [Int.mul_add,Int.mul_sub]
      rw [ih hprev]
      have hp:=topThree_terminal_pair D (c+1) (by omega) (by
        simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hD)
      simp only [Nat.one_add,Int.natCast_add] at hp ⊢
      have h1 : ((1:Nat):Int)=(1:Int) := rfl
      rw [h1] at hp ⊢
      simp only [Nat.succ_eq_add_one] at hp ⊢
      rw [Int.mul_sub] at hp
      omega

private theorem startThreePoly5_minimal_int (x : Int) :
    startThreePoly5 (2*iPow x 2+1) x=
      x*(x+1)*(96*iPow x 3-96*iPow x 2-94*x+109) := by
  have hd2 : (2*iPow x 2+1)*(2*iPow x 2+1)=
      4*iPow x 4+4*iPow x 2+1 := by
    simp only [Int.mul_add,Int.add_mul,Int.mul_one,Int.one_mul]
    have h4 : (2*iPow x 2)*(2*iPow x 2)=4*iPow x 4 := by
      rw [show (4:Int)=2*2 by decide]; dsimp [iPow]; ac_rfl
    rw [h4]
    omega
  have hd3 : (2*iPow x 2+1)*(2*iPow x 2+1)*(2*iPow x 2+1)=
      8*iPow x 6+12*iPow x 4+6*iPow x 2+1 := by
    rw [hd2]
    simp only [Int.mul_add,Int.add_mul,Int.mul_one,Int.one_mul]
    have h6 : 4*iPow x 4*(2*iPow x 2)=8*iPow x 6 := by
      rw [show (8:Int)=4*2 by decide]; dsimp [iPow]; ac_rfl
    have h4 : 4*iPow x 2*(2*iPow x 2)=8*iPow x 4 := by
      rw [show (8:Int)=4*2 by decide]; dsimp [iPow]; ac_rfl
    rw [h6,h4]
    omega
  unfold startThreePoly5 startThreeA startThreeB startThreeC startThreeE
  have h20d3 : 20*(2*iPow x 2+1)*(2*iPow x 2+1)*(2*iPow x 2+1)=
      20*((2*iPow x 2+1)*(2*iPow x 2+1)*(2*iPow x 2+1)) := by ac_rfl
  rw [h20d3,hd3,hd2]
  have hA : 20*(8*iPow x 6+12*iPow x 4+6*iPow x 2+1)*(iPow x 2+x)=
      160*iPow x 8+160*iPow x 7+240*iPow x 6+240*iPow x 5+
      120*iPow x 4+120*iPow x 3+20*iPow x 2+20*x := by
    simp only [Int.mul_add,Int.add_mul]
    have t1 : 20*(8*iPow x 6)*iPow x 2=160*iPow x 8 := by
      rw [show (160:Int)=20*8 by decide]; dsimp [iPow]; ac_rfl
    have t2 : 20*(12*iPow x 4)*iPow x 2=240*iPow x 6 := by
      rw [show (240:Int)=20*12 by decide]; dsimp [iPow]; ac_rfl
    have t3 : 20*(6*iPow x 2)*iPow x 2=120*iPow x 4 := by
      rw [show (120:Int)=20*6 by decide]; dsimp [iPow]; ac_rfl
    have t4 : 20*1*iPow x 2=20*iPow x 2 := by ac_rfl
    have t5 : 20*(8*iPow x 6)*x=160*iPow x 7 := by
      rw [show (160:Int)=20*8 by decide]; dsimp [iPow]; ac_rfl
    have t6 : 20*(12*iPow x 4)*x=240*iPow x 5 := by
      rw [show (240:Int)=20*12 by decide]; dsimp [iPow]; ac_rfl
    have t7 : 20*(6*iPow x 2)*x=120*iPow x 3 := by
      rw [show (120:Int)=20*6 by decide]; dsimp [iPow]; ac_rfl
    have t8 : 20*1*x=20*x := by ac_rfl
    rw [t1,t2,t3,t4,t5,t6,t7,t8]
    omega
  have hB : (4*iPow x 4+4*iPow x 2+1)*
      (-120*iPow x 4-180*iPow x 3-30*iPow x 2+30*x)=
      -480*iPow x 8-720*iPow x 7-600*iPow x 6-600*iPow x 5-
      240*iPow x 4-60*iPow x 3-30*iPow x 2+30*x := by
    simp only [Int.mul_add,Int.add_mul,Int.mul_sub]
    have t1 : 4*iPow x 4*(120*iPow x 4)=480*iPow x 8 := by
      rw [show (480:Int)=4*120 by decide]; dsimp [iPow]; ac_rfl
    have t2 : 4*iPow x 4*(180*iPow x 3)=720*iPow x 7 := by
      rw [show (720:Int)=4*180 by decide]; dsimp [iPow]; ac_rfl
    have t3 : 4*iPow x 4*(30*iPow x 2)=120*iPow x 6 := by
      rw [show (120:Int)=4*30 by decide]; dsimp [iPow]; ac_rfl
    have t4 : 4*iPow x 4*(30*x)=120*iPow x 5 := by
      rw [show (120:Int)=4*30 by decide]; dsimp [iPow]; ac_rfl
    have t5 : 4*iPow x 2*(120*iPow x 4)=480*iPow x 6 := by
      rw [show (480:Int)=4*120 by decide]; dsimp [iPow]; ac_rfl
    have t6 : 4*iPow x 2*(180*iPow x 3)=720*iPow x 5 := by
      rw [show (720:Int)=4*180 by decide]; dsimp [iPow]; ac_rfl
    have t7 : 4*iPow x 2*(30*iPow x 2)=120*iPow x 4 := by
      rw [show (120:Int)=4*30 by decide]; dsimp [iPow]; ac_rfl
    have t8 : 4*iPow x 2*(30*x)=120*iPow x 3 := by
      rw [show (120:Int)=4*30 by decide]; dsimp [iPow]; ac_rfl
    have tn1 : 4*iPow x 4*(-120*iPow x 4)=-480*iPow x 8 := by
      rw [show (-480:Int)=4*(-120) by decide]; dsimp [iPow]; ac_rfl
    have tn5 : 4*iPow x 2*(-120*iPow x 4)=-480*iPow x 6 := by
      rw [show (-480:Int)=4*(-120) by decide]; dsimp [iPow]; ac_rfl
    simp only [Int.mul_neg,Int.one_mul]
    rw [tn1,tn5,t2,t3,t4,t6,t7,t8]
    omega
  have hC : (2*iPow x 2+1)*
      (240*iPow x 6+480*iPow x 5+120*iPow x 4-120*iPow x 3+
        40*iPow x 2+40*x)=
      480*iPow x 8+960*iPow x 7+480*iPow x 6+240*iPow x 5+
      200*iPow x 4-40*iPow x 3+40*iPow x 2+40*x := by
    simp only [Int.mul_add,Int.add_mul,Int.mul_sub]
    have t1 : 2*iPow x 2*(240*iPow x 6)=480*iPow x 8 := by
      rw [show (480:Int)=2*240 by decide]; dsimp [iPow]; ac_rfl
    have t2 : 2*iPow x 2*(480*iPow x 5)=960*iPow x 7 := by
      rw [show (960:Int)=2*480 by decide]; dsimp [iPow]; ac_rfl
    have t3 : 2*iPow x 2*(120*iPow x 4)=240*iPow x 6 := by
      rw [show (240:Int)=2*120 by decide]; dsimp [iPow]; ac_rfl
    have t4 : 2*iPow x 2*(120*iPow x 3)=240*iPow x 5 := by
      rw [show (240:Int)=2*120 by decide]; dsimp [iPow]; ac_rfl
    have t5 : 2*iPow x 2*(40*iPow x 2)=80*iPow x 4 := by
      rw [show (80:Int)=2*40 by decide]; dsimp [iPow]; ac_rfl
    have t6 : 2*iPow x 2*(40*x)=80*iPow x 3 := by
      rw [show (80:Int)=2*40 by decide]; dsimp [iPow]; ac_rfl
    rw [t1,t2,t3,t4,t5,t6]
    omega
  have hR : x*(x+1)*(96*iPow x 3-96*iPow x 2-94*x+109)=
      96*iPow x 5-190*iPow x 3+15*iPow x 2+109*x := by
    simp only [Int.mul_add,Int.add_mul,Int.mul_sub,Int.mul_one]
    have t1 : x*x*(96*iPow x 3)=96*iPow x 5 := by dsimp [iPow]; ac_rfl
    have t2 : x*x*(96*iPow x 2)=96*iPow x 4 := by dsimp [iPow]; ac_rfl
    have t3 : x*x*(94*x)=94*iPow x 3 := by dsimp [iPow]; ac_rfl
    have t4 : x*x*109=109*iPow x 2 := by dsimp [iPow]; ac_rfl
    have t5 : x*(96*iPow x 3)=96*iPow x 4 := by dsimp [iPow]; ac_rfl
    have t6 : x*(96*iPow x 2)=96*iPow x 3 := by dsimp [iPow]; ac_rfl
    have t7 : x*(94*x)=94*iPow x 2 := by dsimp [iPow]; ac_rfl
    rw [t1,t2,t3,t4,t5,t6,t7]
    omega
  rw [hA,hB,hC,hR]
  omega

/-- Exact division-free third-deficit coefficient of the minimal start-one
tail.  This is the identity `30 b₃ = m(m+1)P(m)`. -/
theorem minimalBase_deficit_three (m : Nat) (hm : 0<m) :
    30*reverseTailCoeff (2*m*m+1) 1 (2*m*m-2) (m-1)=
      (m:Int)*((m:Int)+1)*
        (96*iPow (m:Int) 3-96*iPow (m:Int) 2-94*(m:Int)+109) := by
  have hend : 1+(m-1)=m := by omega
  have hD : 2*(1+(m-1))*(1+(m-1))+1≤2*m*m+1 := by
    rw [hend]
    exact Nat.le_refl _
  have ht:=six_mul_reverseTailCoeff_top_three (2*m*m+1) 1 (m-1)
    (by decide) hD
  have h5:=five_reverseTopThreeClosed_start_one (2*m*m+1) (m-1) (by
    have hc : m-1+1=m := by omega
    rw [hc]
    exact Nat.le_refl _)
  have hc : (((m-1):Nat):Int)+1=(m:Int) := by
    have hn : m-1+1=m := by omega
    have hi:=congrArg Int.ofNat hn
    simpa only [Int.natCast_add] using hi
  rw [hc] at h5
  have hd : ((2*m*m+1:Nat):Int)=2*iPow (m:Int) 2+1 := by
    simp only [Int.natCast_add,Int.natCast_mul]
    have h1 : ((1:Nat):Int)=(1:Int) := rfl
    have h2 : ((2:Nat):Int)=(2:Int) := rfl
    rw [h1,h2]
    dsimp [iPow]
    ac_rfl
  rw [hd,startThreePoly5_minimal_int] at h5
  have hidx : 2*m*m+1-3=2*m*m-2 := by omega
  rw [hidx] at ht
  calc
    30*reverseTailCoeff (2*m*m+1) 1 (2*m*m-2) (m-1) =
        5*(6*reverseTailCoeff (2*m*m+1) 1 (2*m*m-2) (m-1)) := by
          rw [show (30:Int)=5*6 by decide]
          ac_rfl
    _ = 5*reverseTopThreeClosed (2*m*m+1) 1 (m-1) := by rw [ht]
    _ = _ := h5

/-- Public multiplication-only form of `minimalBase_deficit_three`.  This
removes the private integer-power implementation from downstream boundary
payment arguments. -/
theorem minimalBase_deficit_three_mul (m : Nat) (hm : 0 < m) :
    30 * reverseTailCoeff (2 * m * m + 1) 1 (2 * m * m - 2) (m - 1) =
      (m : Int) * ((m : Int) + 1) *
        (96 * ((m : Int) * (m : Int) * (m : Int)) -
          96 * ((m : Int) * (m : Int)) - 94 * (m : Int) + 109) := by
  have h := minimalBase_deficit_three m hm
  simpa [iPow, Int.mul_assoc] using h

private def topTwoDiagInt (d x : Int) : Int :=
  4*iPow x 2*(d-2*iPow x 2)*(d-2*iPow x 2)+2*iPow x 2

private def topTwoOffInt (d x : Int) : Int :=
  4*x*(x+1)*(d-(2*x*(x+1)-1))*(d-(2*x*(x+1)-1)-1)

private theorem topTwoDiagInt_generic (d A : Int) :
    4*A*(d-2*A)*(d-2*A)+2*A =
      4*d*d*A-16*d*A*A+16*A*A*A+2*A := by
  simp only [Int.mul_add,Int.add_mul,Int.sub_eq_add_neg,Int.neg_add,Int.mul_neg]
  let z1:=d*d*A
  let z2:=d*A*A
  let z3:=A*A*A
  have h1:4*A*d*d=4*z1 := by dsimp[z1]; ac_rfl
  have h2:4*A*d*(2*A)=8*z2 := by
    dsimp[z2]; rw[show (8:Int)=4*2 by decide]; ac_rfl
  have h3:4*A*(2*A)*d=8*z2 := by
    dsimp[z2]; rw[show (8:Int)=4*2 by decide]; ac_rfl
  have h4:4*A*(2*A)*(2*A)=16*z3 := by
    dsimp[z3]; rw[show (16:Int)=4*2*2 by decide]; ac_rfl
  have h5:4*d*d*A=4*z1 := by dsimp[z1]; ac_rfl
  have h6:16*d*A*A=16*z2 := by dsimp[z2]; ac_rfl
  have h7:16*A*A*A=16*z3 := by dsimp[z3]; ac_rfl
  have hc:(4*A*(2*A))*d=8*d*A*A := by
    rw[show (8:Int)=4*2 by decide]; ac_rfl
  have he:(4*A*(2*A))*(2*A)=16*A*A*A := by
    rw[show (16:Int)=4*2*2 by decide]; ac_rfl
  have hcn:-(4*A*(2*A))*d=-(8*d*A*A) := by rw[Int.neg_mul,hc]
  have hen:-(4*A*(2*A))*(2*A)=-(16*A*A*A) := by rw[Int.neg_mul,he]
  omega

private theorem topTwoDiagInt_expanded (d x : Int) :
    topTwoDiagInt d (x+1) =
      4*d*d*iPow x 2+8*d*d*x+4*d*d
      -16*d*iPow x 4-64*d*iPow x 3-96*d*iPow x 2-64*d*x-16*d
      +16*iPow x 6+96*iPow x 5+240*iPow x 4+320*iPow x 3+
        242*iPow x 2+100*x+18 := by
  unfold topTwoDiagInt
  let A:=iPow (x+1) 2
  change 4*A*(d-2*A)*(d-2*A)+2*A=_
  rw [topTwoDiagInt_generic]
  dsimp [A]
  have hd4 : 16*d*iPow (x+1) 2*iPow (x+1) 2 = 16*d*iPow (x+1) 4 := by
    dsimp [iPow]; ac_rfl
  have h6 : 16*iPow (x+1) 2*iPow (x+1) 2*iPow (x+1) 2 =
      16*iPow (x+1) 6 := by
    dsimp [iPow]; ac_rfl
  rw [hd4,h6,iPow_add_one_two,iPow_add_one_four,iPow_add_one_six,iPow_one]
  simp only [Int.mul_add]
  have ha : 4*d*d*(2*x)=8*d*d*x := by
    rw[show (8:Int)=4*2 by decide]; ac_rfl
  have hb : 16*d*(4*iPow x 3)=64*d*iPow x 3 := by
    rw[show (64:Int)=16*4 by decide]; ac_rfl
  have hc : 16*d*(6*iPow x 2)=96*d*iPow x 2 := by
    rw[show (96:Int)=16*6 by decide]; ac_rfl
  have he : 16*d*(4*x)=64*d*x := by
    rw[show (64:Int)=16*4 by decide]; ac_rfl
  omega

private theorem topTwoOffInt_generic (d X : Int) :
    4*X*(d-2*X+1)*(d-2*X)=
      4*d*d*X-16*d*X*X+16*X*X*X+4*d*X-8*X*X := by
  simp only [Int.mul_add,Int.add_mul,Int.sub_eq_add_neg,Int.neg_add,
    Int.mul_neg,Int.mul_one]
  let z1:=d*d*X
  let z2:=d*X*X
  let z3:=X*X*X
  have h1:4*X*d*d=4*z1 := by dsimp[z1]; ac_rfl
  have h2:4*X*d*(2*X)=8*z2 := by
    dsimp[z2]; rw[show (8:Int)=4*2 by decide]; ac_rfl
  have h3:4*X*(2*X)*d=8*z2 := by
    dsimp[z2]; rw[show (8:Int)=4*2 by decide]; ac_rfl
  have h4:4*X*(2*X)*(2*X)=16*z3 := by
    dsimp[z3]; rw[show (16:Int)=4*2*2 by decide]; ac_rfl
  have h5:4*d*d*X=4*z1 := by dsimp[z1]; ac_rfl
  have h6:16*d*X*X=16*z2 := by dsimp[z2]; ac_rfl
  have h7:16*X*X*X=16*z3 := by dsimp[z3]; ac_rfl
  have hc:(4*X*(2*X))*d=8*d*X*X := by
    rw[show (8:Int)=4*2 by decide]; ac_rfl
  have he:(4*X*(2*X))*(2*X)=16*X*X*X := by
    rw[show (16:Int)=4*2*2 by decide]; ac_rfl
  have hi:4*X*(2*X)=8*X*X := by
    rw[show (8:Int)=4*2 by decide]; ac_rfl
  have hcn:-(4*X*(2*X))*d=-(8*d*X*X) := by rw[Int.neg_mul,hc]
  have hen:-(4*X*(2*X))*(2*X)=-(16*X*X*X) := by rw[Int.neg_mul,he]
  have hdx:4*X*d=4*d*X := by ac_rfl
  omega

private theorem topTwoOffInt_expanded (d x : Int) :
    topTwoOffInt d x =
      4*d*d*iPow x 2+4*d*d*x
      -16*d*iPow x 4-32*d*iPow x 3-12*d*iPow x 2+4*d*x
      +16*iPow x 6+48*iPow x 5+40*iPow x 4-8*iPow x 2 := by
  unfold topTwoOffInt
  let X:=x*(x+1)
  have hX : X=iPow x 2+x := by
    dsimp [X,iPow]
    simp only [Int.mul_add,Int.mul_one]
  have hleft : 4*x*(x+1)=4*X := by dsimp [X]; ac_rfl
  have hp : 2*x*(x+1)=2*X := by dsimp [X]; ac_rfl
  rw [hleft,hp]
  change 4*X*(d-(2*X-1))*(d-(2*X-1)-1)=_
  have hs1 : d-(2*X-1)=d-2*X+1 := by omega
  have hs2 : d-2*X+1-1=d-2*X := by omega
  rw [hs1,hs2,topTwoOffInt_generic]
  have hX2 : X*X=iPow x 4+2*iPow x 3+iPow x 2 := by
    rw [hX]
    simp only [Int.mul_add,Int.add_mul]
    have h4 : iPow x 2*iPow x 2=iPow x 4 := by dsimp [iPow]; ac_rfl
    have h3a : iPow x 2*x=iPow x 3 := by dsimp [iPow]; ac_rfl
    have h3b : x*iPow x 2=iPow x 3 := by dsimp [iPow]
    have hx2 : x*x=iPow x 2 := by dsimp [iPow]; rw [Int.mul_one]
    rw [h4,h3a,h3b,hx2]
    omega
  have hX3 : X*X*X=iPow x 6+3*iPow x 5+3*iPow x 4+iPow x 3 := by
    rw [hX2,hX]
    simp only [Int.mul_add,Int.add_mul]
    have h42 : iPow x 4*iPow x 2=iPow x 6 := by dsimp [iPow]; ac_rfl
    have h32 : iPow x 3*iPow x 2=iPow x 5 := by dsimp [iPow]; ac_rfl
    have h22 : iPow x 2*iPow x 2=iPow x 4 := by dsimp [iPow]; ac_rfl
    have h4x : iPow x 4*x=iPow x 5 := by dsimp [iPow]; ac_rfl
    have h3x : iPow x 3*x=iPow x 4 := by dsimp [iPow]; ac_rfl
    have h2x : iPow x 2*x=iPow x 3 := by dsimp [iPow]; ac_rfl
    have h32c : 2*iPow x 3*iPow x 2=2*iPow x 5 := by dsimp [iPow]; ac_rfl
    have h3xc : 2*iPow x 3*x=2*iPow x 4 := by dsimp [iPow]; ac_rfl
    omega
  have hdX2 : -16*d*X*X=-16*d*(iPow x 4+2*iPow x 3+iPow x 2) := by
    have h:=congrArg (fun z:Int=>-16*d*z) hX2
    simpa only [Int.mul_assoc] using h
  have h16X3 : 16*X*X*X=16*(iPow x 6+3*iPow x 5+3*iPow x 4+iPow x 3) := by
    have h:=congrArg (fun z:Int=>16*z) hX3
    simpa only [Int.mul_assoc] using h
  have hm8X2 : -8*X*X=-8*(iPow x 4+2*iPow x 3+iPow x 2) := by
    have h:=congrArg (fun z:Int=>-8*z) hX2
    simpa only [Int.mul_assoc] using h
  have hDlin : 4*d*d*X=4*d*d*(iPow x 2+x) := by rw [hX]
  have hdlin : 4*d*X=4*d*(iPow x 2+x) := by rw [hX]
  have hp16 : 16*d*X*X=16*d*(iPow x 4+2*iPow x 3+iPow x 2) := by
    have h:=congrArg (fun z:Int=>16*d*z) hX2
    simpa only [Int.mul_assoc] using h
  have hp8 : 8*X*X=8*(iPow x 4+2*iPow x 3+iPow x 2) := by
    have h:=congrArg (fun z:Int=>8*z) hX2
    simpa only [Int.mul_assoc] using h
  simp only [Int.mul_add] at hDlin hdlin hdX2 h16X3 hm8X2
  simp only [Int.mul_add] at hp16 hp8
  have hc32 : 16*d*(2*iPow x 3)=32*d*iPow x 3 := by
    rw [show (32:Int)=16*2 by decide]
    ac_rfl
  have hc16 : 4*d*iPow x 2+12*d*iPow x 2=16*d*iPow x 2 := by
    have h:(16:Int)*d=4*d+12*d := by omega
    rw [h,Int.add_mul]
  omega

private theorem topTwo_terminal_pair_int (d x : Int) :
    topTwoDiagInt d (x+1)-topTwoOffInt d x=startTwoDelta d x := by
  rw [topTwoDiagInt_expanded, topTwoOffInt_expanded]
  unfold startTwoDelta
  simp only [Int.mul_assoc]
  omega

/-- The compact terminal diagonal/off-diagonal pair is exactly the increment
of the start-one deficit-two polynomial. -/
theorem topTwo_terminal_pair (D m : Nat) :
    topTwoDiagClosed D (m+1)-topTwoOffClosed D m =
      startTwoPoly (D:Int) ((m:Int)+1)-startTwoPoly (D:Int) (m:Int) := by
  have hp := topTwo_terminal_pair_int (D:Int) (m:Int)
  have hd : topTwoDiagClosed D (m+1) =
      topTwoDiagInt (D:Int) ((m:Int)+1) := by
    unfold topTwoDiagClosed topTwoDiagInt
    simp only [Int.natCast_add]
    have h1 : ((1:Nat):Int)=(1:Int) := rfl
    rw [h1]
    dsimp [iPow]
    ac_rfl
  have ho : topTwoOffClosed D m = topTwoOffInt (D:Int) (m:Int) := by
    unfold topTwoOffClosed topTwoOffInt
    dsimp [iPow]
  rw [hd,ho]
  rw [startTwoPoly_step]
  omega

/-- Every start-one deficit-two closed tail is the canonical polynomial at
its terminal index. -/
theorem reverseTopTwoClosed_start_one (D c : Nat) :
    reverseTopTwoClosed D 1 c = startTwoPoly (D:Int) ((c:Int)+1) := by
  induction c with
  | zero =>
      simp [reverseTopTwoClosed, topTwoDiagClosed, startTwoPoly, iPow]
      have hs : ((D:Int)-2)*((D:Int)-2) =
          (D:Int)*(D:Int)-4*(D:Int)+4 := by
        simp only [Int.sub_mul,Int.mul_sub]
        omega
      have hfour : 4*((D:Int)-2)*((D:Int)-2) =
          4*(((D:Int)-2)*((D:Int)-2)) := by ac_rfl
      rw [hfour]
      rw [hs]
      simp only [Int.mul_assoc]
      omega
  | succ c ih =>
      rw [reverseTopTwoClosed_append]
      rw [ih]
      simp only [Nat.one_add]
      have hp := topTwo_terminal_pair D (c+1)
      simp only [Int.natCast_add] at hp ⊢
      have h1 : ((1:Nat):Int)=(1:Int) := rfl
      rw [h1] at hp ⊢
      simp only [Nat.succ_eq_add_one] at hp ⊢
      omega

private theorem startTwoPoly_minimal_int (x : Int) :
    startTwoPoly (2*iPow x 2+1) x = -3*x*(x+1)*(2*x-3) := by
  unfold startTwoPoly
  have hA : 2*(2*iPow x 2+1)*(2*iPow x 2+1)*iPow x 2 =
      8*iPow x 6+8*iPow x 4+2*iPow x 2 := by
    simp only [Int.mul_add,Int.add_mul]
    have t1:2*(2*iPow x 2)*(2*iPow x 2)*iPow x 2=8*iPow x 6:=by
      rw[show (8:Int)=2*2*2 by decide];dsimp[iPow];ac_rfl
    have t2:2*1*(2*iPow x 2)*iPow x 2=4*iPow x 4:=by
      rw[show (4:Int)=2*2 by decide];dsimp[iPow];ac_rfl
    have t3:2*(2*iPow x 2)*1*iPow x 2=4*iPow x 4:=by
      rw[show (4:Int)=2*2 by decide];dsimp[iPow];ac_rfl
    have t4:2*1*1*iPow x 2=2*iPow x 2:=by ac_rfl
    rw[t1,t2,t3,t4];omega
  have hB : 2*(2*iPow x 2+1)*(2*iPow x 2+1)*x =
      8*iPow x 5+8*iPow x 3+2*x := by
    simp only [Int.mul_add,Int.add_mul]
    have t1:2*(2*iPow x 2)*(2*iPow x 2)*x=8*iPow x 5:=by
      rw[show (8:Int)=2*2*2 by decide];dsimp[iPow];ac_rfl
    have t2:2*1*(2*iPow x 2)*x=4*iPow x 3:=by
      rw[show (4:Int)=2*2 by decide];dsimp[iPow];ac_rfl
    have t3:2*(2*iPow x 2)*1*x=4*iPow x 3:=by
      rw[show (4:Int)=2*2 by decide];dsimp[iPow];ac_rfl
    have t4:2*1*1*x=2*x:=by ac_rfl
    rw[t1,t2,t3,t4];omega
  have hC : 8*(2*iPow x 2+1)*iPow x 4=16*iPow x 6+8*iPow x 4 := by
    simp only[Int.mul_add]
    simp only[Int.add_mul]
    have t:8*(2*iPow x 2)*iPow x 4=16*iPow x 6:=by
      rw[show (16:Int)=8*2 by decide];dsimp[iPow];ac_rfl
    rw[t];omega
  have hD : 12*(2*iPow x 2+1)*iPow x 3=24*iPow x 5+12*iPow x 3 := by
    simp only[Int.mul_add]
    simp only[Int.add_mul]
    have t:12*(2*iPow x 2)*iPow x 3=24*iPow x 5:=by
      rw[show (24:Int)=12*2 by decide];dsimp[iPow];ac_rfl
    rw[t];omega
  have hE : 4*(2*iPow x 2+1)*x=8*iPow x 3+4*x := by
    simp only[Int.mul_add]
    simp only[Int.add_mul]
    have t:4*(2*iPow x 2)*x=8*iPow x 3:=by
      rw[show (8:Int)=4*2 by decide];dsimp[iPow];ac_rfl
    rw[t];omega
  rw[hA,hB,hC,hD,hE]
  have hR : -3*x*(x+1)*(2*x-3)=-6*iPow x 3+3*iPow x 2+9*x := by
    simp only[Int.mul_add,Int.mul_sub]
    simp only[Int.add_mul]
    dsimp[iPow]
    simp only[Int.mul_one,Int.mul_assoc]
    have h6:-3*(x*(x*(2*x)))=-6*(x*(x*x)):=by
      rw[show (-6:Int)=(-3)*2 by decide];ac_rfl
    have hq:-3*(x*(2*x))=-6*(x*x):=by
      rw[show (-6:Int)=(-3)*2 by decide];ac_rfl
    have hq3:-3*(x*(x*3))=-9*(x*x):=by
      rw[show (-9:Int)=(-3)*3 by decide];ac_rfl
    have hx3:-3*(x*3)=-9*x:=by
      rw[show (-9:Int)=(-3)*3 by decide];ac_rfl
    rw[h6,hq,hq3,hx3]
    omega
  rw[hR]
  omega

/-- The deficit-two coefficient of the minimal start-one tail has its exact
negative closed form. -/
theorem minimalBase_deficit_two (m : Nat) (hm : 0 < m) :
    reverseTailCoeff (2*m*m+1) 1 (2*m*m-1) (m-1) =
      -(3*(m:Int)*((m:Int)+1)*(2*(m:Int)-3)) := by
  have hend : 1+(m-1)=m := by omega
  have hD : 2*(1+(m-1))*(1+(m-1))+1 ≤ 2*m*m+1 := by
    rw [hend]
    exact Nat.le_refl _
  have ht := two_mul_reverseTailCoeff_top_two (2*m*m+1) 1 (m-1)
    (by decide) hD
  rw [reverseTopTwoClosed_start_one] at ht
  have hc : (((m-1):Nat):Int)+1=(m:Int) := by
    have hn : m-1+1=m := by omega
    have hi := congrArg Int.ofNat hn
    simpa only [Int.natCast_add] using hi
  rw [hc] at ht
  have hd : ((2*m*m+1:Nat):Int)=2*iPow (m:Int) 2+1 := by
    simp only [Int.natCast_add,Int.natCast_mul]
    have h1 : ((1:Nat):Int)=(1:Int) := rfl
    have h2 : ((2:Nat):Int)=(2:Int) := rfl
    rw [h1,h2]
    dsimp [iPow]
    ac_rfl
  rw [hd,startTwoPoly_minimal_int] at ht
  have hidx : 2*m*m+1-2=2*m*m-1 := by omega
  rw [← hidx]
  have hneg : -(3*(m:Int)*((m:Int)+1)*(2*(m:Int)-3)) =
      -3*(m:Int)*((m:Int)+1)*(2*(m:Int)-3) := by
    rw [show (-3:Int)=-(3:Int) by decide]
    rw [Int.neg_mul,Int.neg_mul,Int.neg_mul]
  rw [hneg]
  omega

/-- The minimal deficit-two base is strictly negative from terminal cell two
onward. -/
theorem minimalBase_deficit_two_negative (m : Nat) (hm : 2 ≤ m) :
    reverseTailCoeff (2*m*m+1) 1 (2*m*m-1) (m-1) < 0 := by
  rw [minimalBase_deficit_two m (by omega)]
  have hx2 : (2:Int) ≤ (m:Int) := Int.ofNat_le.mpr hm
  have h3 : (0:Int) < 3 := by decide
  have hm0 : (0:Int) < (m:Int) := by omega
  have hm1 : (0:Int) < (m:Int)+1 := by omega
  have hf : (0:Int) < 2*(m:Int)-3 := by omega
  have h3m : (0:Int) < 3*(m:Int) := Int.mul_pos h3 hm0
  have h3m1 : (0:Int) < 3*(m:Int)*((m:Int)+1) := Int.mul_pos h3m hm1
  have hp : (0:Int) < 3*(m:Int)*((m:Int)+1)*(2*(m:Int)-3) :=
    Int.mul_pos h3m1 hf
  omega

/-! ## Through-`b₃` adjacent-binomial payment

The long-range payment is a two-variable polynomial inequality after the
shifts `m=u+2`, `r=a+6`.  We reflect its exact positive-coefficient slack
through the constructive `Q'` ring normaliser, then transport the resulting
identity back to `Int`.  No untrusted polynomial tactic is used. -/

private def certIntPow (x : Int) : Nat → Int
  | 0 => 1
  | n + 1 => certIntPow x n * x

private def certIntEval (rho : Nat → Int) :
    RingNormaliser.PolyExpr → Int
  | .const c => c
  | .var i => rho i
  | .add x y => certIntEval rho x + certIntEval rho y
  | .mul x y => certIntEval rho x * certIntEval rho y
  | .neg x => -(certIntEval rho x)
  | .pow x n => certIntPow (certIntEval rho x) n

private theorem cert_ofInt_neg (x : Int) :
    (-(Q'.ofInt x)).eqv (Q'.ofInt (-x)) := by
  rfl

private theorem cert_qpow_ofInt (x : Int) : ∀ n,
    (RingNormaliser.qpow (Q'.ofInt x) n).eqv
      (Q'.ofInt (certIntPow x n))
  | 0 => by exact Q'.eqv_refl _
  | n + 1 => by
      exact Q'.eqv_trans _ (Q'.ofInt (certIntPow x n) * Q'.ofInt x) _
        (Q'.mul_eqv_congr_right _ _ _ (cert_qpow_ofInt x n))
        (Q'.eqv_symm (RingNormaliser.ofInt_mul (certIntPow x n) x))

private theorem cert_eval_ofInt (rho : Nat → Int) : ∀ e,
    (RingNormaliser.eval (fun i => Q'.ofInt (rho i)) e).eqv
      (Q'.ofInt (certIntEval rho e))
  | .const _ => Q'.eqv_refl _
  | .var _ => Q'.eqv_refl _
  | .add x y => by
      exact Q'.eqv_trans _
        (Q'.ofInt (certIntEval rho x) +
          RingNormaliser.eval (fun i => Q'.ofInt (rho i)) y) _
        (Q'.add_eqv_congr_right _ _ _ (cert_eval_ofInt rho x))
        (Q'.eqv_trans _
          (Q'.ofInt (certIntEval rho x) + Q'.ofInt (certIntEval rho y)) _
          (Q'.add_eqv_congr_left _ _ _ (cert_eval_ofInt rho y))
          (Q'.eqv_symm (RingNormaliser.ofInt_add _ _)))
  | .mul x y => by
      exact Q'.eqv_trans _
        (Q'.ofInt (certIntEval rho x) *
          RingNormaliser.eval (fun i => Q'.ofInt (rho i)) y) _
        (Q'.mul_eqv_congr_right _ _ _ (cert_eval_ofInt rho x))
        (Q'.eqv_trans _
          (Q'.ofInt (certIntEval rho x) * Q'.ofInt (certIntEval rho y)) _
          (Q'.mul_eqv_congr_left _ _ _ (cert_eval_ofInt rho y))
          (Q'.eqv_symm (RingNormaliser.ofInt_mul _ _)))
  | .neg x => by
      exact Q'.eqv_trans _ (-(Q'.ofInt (certIntEval rho x))) _
        (Q'.neg_eqv_congr _ _ (cert_eval_ofInt rho x))
        (cert_ofInt_neg _)
  | .pow x n => by
      exact Q'.eqv_trans _
        (RingNormaliser.qpow (Q'.ofInt (certIntEval rho x)) n) _
        (RingNormaliser.qpow_eqv_congr (cert_eval_ofInt rho x) n)
        (cert_qpow_ofInt _ n)

private theorem cert_int_poly_identity
    (e₁ e₂ : RingNormaliser.PolyExpr)
    (hn : RingNormaliser.normalize e₁ = RingNormaliser.normalize e₂)
    (rho : Nat → Int) : certIntEval rho e₁ = certIntEval rho e₂ := by
  have h := RingNormaliser.poly_identity_of_normal_eq e₁ e₂ hn
    (fun i => Q'.ofInt (rho i))
  have hl := cert_eval_ofInt rho e₁
  have hr := cert_eval_ofInt rho e₂
  have hi := Q'.eqv_trans _ _ _ (Q'.eqv_symm hl)
    (Q'.eqv_trans _ _ _ h hr)
  unfold Q'.eqv at hi
  change certIntEval rho e₁ * 1 = certIntEval rho e₂ * 1 at hi
  simpa using hi

private def certAdd (x y : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr := .add x y
private def certMul (x y : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr := .mul x y
private def certNeg (x : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr := .neg x
private def certSub (x y : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr := certAdd x (certNeg y)
private def certConst (z : Int) : RingNormaliser.PolyExpr := .const z
private def certScale (z : Int) (x : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr := certMul (certConst z) x

private def adjacentScalarLHS : RingNormaliser.PolyExpr :=
  let u := RingNormaliser.PolyExpr.var 0
  let a := RingNormaliser.PolyExpr.var 1
  let m := certAdd u (certConst 2)
  let q := certSub (certAdd (certScale 4 u) (certConst 4)) a
  let p := certAdd (certScale 96 (.pow m 3))
    (certAdd (certScale (-96) (.pow m 2))
      (certAdd (certScale (-94) m) (certConst 109)))
  certSub
    (certMul (certMul (certAdd a (certConst 5))
      (certAdd a (certConst 4))) p)
    (certScale 30
      (certAdd
        (certMul (certMul (certAdd (certScale 4 m) (certConst (-10)))
          (certAdd q (certConst 3))) (certAdd q (certConst 2)))
        (certMul (certMul (certAdd (certScale 6 m) (certConst (-9)))
          (certAdd q (certConst 3))) (certAdd a (certConst 5)))))

private def adjacentScalarRHS : RingNormaliser.PolyExpr :=
  let u := RingNormaliser.PolyExpr.var 0
  let a := RingNormaliser.PolyExpr.var 1
  certAdd (certScale 96 (certMul (.pow u 3) (.pow a 2)))
  (certAdd (certScale 864 (certMul (.pow u 3) a))
  (certAdd (certScale 480 (certMul (.pow u 2) (.pow a 2)))
  (certAdd (certScale 4560 (certMul (.pow u 2) a))
  (certAdd (certScale 720 (.pow u 2))
  (certAdd (certScale 734 (certMul u (.pow a 2)))
  (certAdd (certScale 6426 (certMul u a))
  (certAdd (certScale 3460 u)
  (certAdd (certScale 455 (.pow a 2))
  (certAdd (certScale 1785 a) (certConst 5470))))))))))

private theorem adjacentScalar_normal :
    RingNormaliser.normalize adjacentScalarLHS =
      RingNormaliser.normalize adjacentScalarRHS := by
  decide

private theorem adjacentScalar_expansion (u a : Int) :
    (a+5)*(a+4)*(96*((u+2)*(u+2)*(u+2))+
      ((-96)*((u+2)*(u+2))+((-94)*(u+2)+109)))
      + -(30*((4*(u+2)+(-10))*(4*u+4+(-a)+3)*(4*u+4+(-a)+2)
        +(6*(u+2)+(-9))*(4*u+4+(-a)+3)*(a+5))) =
    96*(u*u*u*(a*a))+
      (864*(u*u*u*a)+
      (480*(u*u*(a*a))+
      (4560*(u*u*a)+
      (720*(u*u)+
      (734*(u*(a*a))+
        (6426*(u*a)+(3460*u+(455*(a*a)+(1785*a+5470))))))))) := by
  have h := cert_int_poly_identity adjacentScalarLHS adjacentScalarRHS
    adjacentScalar_normal (fun i => if i = 0 then u else a)
  simpa [adjacentScalarLHS, adjacentScalarRHS, certAdd, certMul, certNeg,
    certSub, certConst, certScale, certIntEval, certIntPow,
    Int.sub_eq_add_neg] using h

/-- Positive scalar certificate that pays both negative adjacent coordinates
after the `b₃` term, valid throughout the long boundary range `r≥6`. -/
theorem throughThree_adjacent_scalar_payment (m r q : Nat)
    (hm : 2 ≤ m) (hr : 6 ≤ r) (hqr : q + r = 4*m+2) :
    30*((4*(m:Int)+(-10))*((q:Int)+3)*((q:Int)+2)+
      (6*(m:Int)+(-9))*((q:Int)+3)*((r:Int)-1)) ≤
    ((r:Int)-1)*((r:Int)-2)*
      (96*((m:Int)*(m:Int)*(m:Int))+
        ((-96)*((m:Int)*(m:Int))+((-94)*(m:Int)+109))) := by
  let u := m-2
  let a := r-6
  have hum : u+2=m := by dsimp [u]; omega
  have har : a+6=r := by dsimp [a]; omega
  have hui : (u:Int)+2=(m:Int) := by
    have h := congrArg Int.ofNat hum
    simpa only [Int.ofNat_eq_natCast, Int.natCast_add] using h
  have hai : (a:Int)+6=(r:Int) := by
    have h := congrArg Int.ofNat har
    simpa only [Int.ofNat_eq_natCast, Int.natCast_add] using h
  have hqri : (q:Int)+(r:Int)=4*(m:Int)+2 := by
    have h := congrArg Int.ofNat hqr
    simpa only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul] using h
  have hqi : 4*(u:Int)+4+(-(a:Int))=(q:Int) := by omega
  have ha5 : (a:Int)+5=(r:Int)-1 := by omega
  have ha4 : (a:Int)+4=(r:Int)-2 := by omega
  have he := adjacentScalar_expansion (u:Int) (a:Int)
  rw [hui, hqi, ha5, ha4] at he
  let N : Nat :=
    96*(u*u*u*(a*a))+
      (864*(u*u*u*a)+
      (480*(u*u*(a*a))+
      (4560*(u*u*a)+
      (720*(u*u)+
      (734*(u*(a*a))+
        (6426*(u*a)+(3460*u+(455*(a*a)+(1785*a+5470)))))))))
  have hcast :
      96*((u:Int)*(u:Int)*(u:Int)*((a:Int)*(a:Int)))+
        (864*((u:Int)*(u:Int)*(u:Int)*(a:Int))+
        (480*((u:Int)*(u:Int)*((a:Int)*(a:Int)))+
        (4560*((u:Int)*(u:Int)*(a:Int))+
        (720*((u:Int)*(u:Int))+
        (734*((u:Int)*((a:Int)*(a:Int)))+
          (6426*((u:Int)*(a:Int))+
            (3460*(u:Int)+(455*((a:Int)*(a:Int))+(1785*(a:Int)+5470)))))))))
        = Int.ofNat N := by
    dsimp [N]
  have hnonneg : (0:Int) ≤
      96*((u:Int)*(u:Int)*(u:Int)*((a:Int)*(a:Int)))+
        (864*((u:Int)*(u:Int)*(u:Int)*(a:Int))+
        (480*((u:Int)*(u:Int)*((a:Int)*(a:Int)))+
        (4560*((u:Int)*(u:Int)*(a:Int))+
        (720*((u:Int)*(u:Int))+
        (734*((u:Int)*((a:Int)*(a:Int)))+
          (6426*((u:Int)*(a:Int))+
            (3460*(u:Int)+(455*((a:Int)*(a:Int))+(1785*(a:Int)+5470))))))))) := by
    rw [hcast]
    exact Int.natCast_nonneg N
  omega

/-- The exact adjacent-binomial payment supplied by `b₃`.  The two negative
coordinates `b₁,b₂` are paid simultaneously; the proof clears the two
adjacent-binomial denominators and cancels the positive factor
`(r-1)(r-2)`. -/
theorem throughThree_adjacent_binomial_payment (m r : Nat)
    (hm : 2 ≤ m) (hr : 6 ≤ r) (hrS : r ≤ 4*m+2) :
    30*((4*(m:Int)+(-10))*
          (PNPaths.choose (4*m+2) (r-1):Int)+
        (6*(m:Int)+(-9))*
          (PNPaths.choose (4*m+2) (r-2):Int)) ≤
      (96*((m:Int)*(m:Int)*(m:Int))+
        ((-96)*((m:Int)*(m:Int))+((-94)*(m:Int)+109)))*
          (PNPaths.choose (4*m+2) (r-3):Int) := by
  let S := 4*m+2
  let q := S-r
  have hqr : q+r=4*m+2 := by dsimp [q,S]; omega
  have hs := throughThree_adjacent_scalar_payment m r q hm hr hqr
  have h23 := choose_adjacent_cross S (r-3) (by dsimp [S]; omega)
  have h12 := choose_adjacent_cross S (r-2) (by dsimp [S]; omega)
  have hr3 : r-3+1=r-2 := by omega
  have hr2 : r-2+1=r-1 := by omega
  have hS3 : S-(r-3)=q+3 := by dsimp [q]; omega
  have hS2 : S-(r-2)=q+2 := by dsimp [q]; omega
  rw [hr3,hS3] at h23
  rw [hr2,hS2] at h12
  have h23i := congrArg Int.ofNat h23
  have h12i := congrArg Int.ofNat h12
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add] at h23i h12i
  let C₁ : Int := PNPaths.choose S (r-1)
  let C₂ : Int := PNPaths.choose S (r-2)
  let C₃ : Int := PNPaths.choose S (r-3)
  have h23' : ((r:Int)-2)*C₂=((q:Int)+3)*C₃ := by
    dsimp [C₂,C₃]
    have hr2i : ((r-2:Nat):Int)=(r:Int)-2 := by omega
    rw [← hr2i]
    exact h23i
  have h12' : ((r:Int)-1)*C₁=((q:Int)+2)*C₂ := by
    dsimp [C₁,C₂]
    have hr1i : ((r-1:Nat):Int)=(r:Int)-1 := by omega
    rw [← hr1i]
    exact h12i
  have hC₁ :
      (((r:Int)-1)*((r:Int)-2))*C₁=
        (((q:Int)+3)*((q:Int)+2))*C₃ := by
    calc
      (((r:Int)-1)*((r:Int)-2))*C₁ =
          ((r:Int)-2)*(((r:Int)-1)*C₁) := by ac_rfl
      _ = ((r:Int)-2)*(((q:Int)+2)*C₂) := by rw [h12']
      _ = ((q:Int)+2)*(((r:Int)-2)*C₂) := by ac_rfl
      _ = ((q:Int)+2)*(((q:Int)+3)*C₃) := by rw [h23']
      _ = (((q:Int)+3)*((q:Int)+2))*C₃ := by ac_rfl
  have hC₂ :
      (((r:Int)-1)*((r:Int)-2))*C₂=
        (((q:Int)+3)*((r:Int)-1))*C₃ := by
    calc
      (((r:Int)-1)*((r:Int)-2))*C₂ =
          ((r:Int)-1)*(((r:Int)-2)*C₂) := by ac_rfl
      _ = ((r:Int)-1)*(((q:Int)+3)*C₃) := by rw [h23']
      _ = (((q:Int)+3)*((r:Int)-1))*C₃ := by ac_rfl
  let A : Int := 4*(m:Int)+(-10)
  let B : Int := 6*(m:Int)+(-9)
  let P : Int := 96*((m:Int)*(m:Int)*(m:Int))+
    ((-96)*((m:Int)*(m:Int))+((-94)*(m:Int)+109))
  let K : Int := ((r:Int)-1)*((r:Int)-2)
  have hleft : K*(30*(A*C₁+B*C₂))=
      (30*(A*((q:Int)+3)*((q:Int)+2)+
        B*((q:Int)+3)*((r:Int)-1)))*C₃ := by
    calc
      K*(30*(A*C₁+B*C₂))=
          30*(A*(K*C₁)+B*(K*C₂)) := by
            dsimp [K]
            simp only [Int.mul_add]
            ac_rfl
      _ = 30*(A*((((q:Int)+3)*((q:Int)+2))*C₃)+
          B*((((q:Int)+3)*((r:Int)-1))*C₃)) := by rw [hC₁,hC₂]
      _ = 30*((A*((q:Int)+3)*((q:Int)+2))*C₃+
          (B*((q:Int)+3)*((r:Int)-1))*C₃) := by
            congr 2 <;> ac_rfl
      _ = (30*(A*((q:Int)+3)*((q:Int)+2)+
          B*((q:Int)+3)*((r:Int)-1)))*C₃ := by
            rw [← Int.add_mul]
            ac_rfl
  have hright : K*(P*C₃)=(K*P)*C₃ := by ac_rfl
  have hC₃nonneg : (0:Int) ≤ C₃ := by
    dsimp [C₃]
    exact Int.natCast_nonneg _
  have hmul := Int.mul_le_mul_of_nonneg_right hs hC₃nonneg
  have hscaled : K*(30*(A*C₁+B*C₂)) ≤ K*(P*C₃) := by
    rw [hleft,hright]
    exact hmul
  have hKpos : (0:Int)<K := by
    dsimp [K]
    exact Int.mul_pos (by omega) (by omega)
  have hcancel := Int.le_of_mul_le_mul_left hscaled hKpos
  dsimp [A,B,P,C₁,C₂,C₃,S] at hcancel
  exact hcancel

/-! ## The exceptional boundary coordinates `r=4,5` -/

private theorem two_choose_two (n : Nat) (hn : 2 ≤ n) :
    2*PNPaths.choose n 2=n*(n-1) := by
  have h := choose_adjacent_cross n 1 (by omega)
  rw [show 1+1=2 by decide, choose_one] at h
  calc
    2*PNPaths.choose n 2=(n-1)*n := h
    _=n*(n-1) := by ac_rfl

private theorem six_choose_three (n : Nat) (hn : 3 ≤ n) :
    6*PNPaths.choose n 3=n*(n-1)*(n-2) := by
  have h := choose_adjacent_cross n 2 (by omega)
  rw [show 2+1=3 by decide] at h
  calc
    6*PNPaths.choose n 3=2*(3*PNPaths.choose n 3) := by
      rw [show 6=2*3 by decide]
      ac_rfl
    _=2*((n-2)*PNPaths.choose n 2) := by rw [h]
    _=(n-2)*(2*PNPaths.choose n 2) := by ac_rfl
    _=(n-2)*(n*(n-1)) := by rw [two_choose_two n (by omega)]
    _=n*(n-1)*(n-2) := by ac_rfl

private theorem twentyFour_choose_four (n : Nat) (hn : 4 ≤ n) :
    24*PNPaths.choose n 4=n*(n-1)*(n-2)*(n-3) := by
  have h := choose_adjacent_cross n 3 (by omega)
  rw [show 3+1=4 by decide] at h
  calc
    24*PNPaths.choose n 4=6*(4*PNPaths.choose n 4) := by
      rw [show 24=6*4 by decide]
      ac_rfl
    _=6*((n-3)*PNPaths.choose n 3) := by rw [h]
    _=(n-3)*(6*PNPaths.choose n 3) := by ac_rfl
    _=(n-3)*(n*(n-1)*(n-2)) := by
      rw [six_choose_three n (by omega)]
    _=n*(n-1)*(n-2)*(n-3) := by ac_rfl

private theorem oneTwenty_choose_five (n : Nat) (hn : 5 ≤ n) :
    120*PNPaths.choose n 5=n*(n-1)*(n-2)*(n-3)*(n-4) := by
  have h := choose_adjacent_cross n 4 (by omega)
  rw [show 4+1=5 by decide] at h
  calc
    120*PNPaths.choose n 5=24*(5*PNPaths.choose n 5) := by
      rw [show 120=24*5 by decide]
      ac_rfl
    _=24*((n-4)*PNPaths.choose n 4) := by rw [h]
    _=(n-4)*(24*PNPaths.choose n 4) := by ac_rfl
    _=(n-4)*(n*(n-1)*(n-2)*(n-3)) := by
      rw [twentyFour_choose_four n (by omega)]
    _=n*(n-1)*(n-2)*(n-3)*(n-4) := by ac_rfl

/-- Cleared through-`b₃` Pascal remainder at boundary coordinate `r`.
All coefficients are exact integers; in particular the factor `30` clears
the third-deficit coefficient from `minimalBase_deficit_three`. -/
def throughThreeRemainder30 (m r : Nat) : Int :=
  120*(PNPaths.choose (4*m+2) r:Int)+
  30*((-4)*(m:Int)+10)*(PNPaths.choose (4*m+2) (r-1):Int)+
  30*((-6)*(m:Int)+9)*(PNPaths.choose (4*m+2) (r-2):Int)+
  (96*((m:Int)*(m:Int)*(m:Int))+
    ((-96)*((m:Int)*(m:Int))+((-94)*(m:Int)+109)))*
      (PNPaths.choose (4*m+2) (r-3):Int)+
  (-240)*(PNPaths.choose (2*m+4) r:Int)

private def certFalling (x : RingNormaliser.PolyExpr) :
    Nat → RingNormaliser.PolyExpr
  | 0 => certConst 1
  | k + 1 => certMul (certFalling x k) (certAdd x (certConst (-(k:Int))))

private def boundaryFourLHS : RingNormaliser.PolyExpr :=
  let m := RingNormaliser.PolyExpr.var 0
  let S := certAdd (certScale 4 m) (certConst 2)
  let T := certAdd (certScale 2 m) (certConst 4)
  let A := certAdd (certScale (-4) m) (certConst 10)
  let B := certAdd (certScale (-6) m) (certConst 9)
  let P := certAdd (certScale 96 (.pow m 3))
    (certAdd (certScale (-96) (.pow m 2))
      (certAdd (certScale (-94) m) (certConst 109)))
  certAdd (certScale 5 (certFalling S 4))
  (certAdd (certScale 5 (certMul A (certFalling S 3)))
  (certAdd (certScale 15 (certMul B (certFalling S 2)))
  (certAdd (certMul P S) (certScale (-10) (certFalling T 4)))))

private def boundaryFourRHS : RingNormaliser.PolyExpr :=
  let m := RingNormaliser.PolyExpr.var 0
  certScale 8 (certMul (.pow (certAdd (certScale 2 m) (certConst 1)) 2)
    (certAdd (certScale 7 (.pow m 2))
      (certAdd (certScale 7 m) (certConst 31))))

private theorem boundaryFour_normal :
    RingNormaliser.normalize boundaryFourLHS =
      RingNormaliser.normalize boundaryFourRHS := by
  set_option maxRecDepth 10000 in
    decide

private theorem boundaryFour_factor_identity (m : Int) :
    5*((4*m+2)*(4*m+2-1)*(4*m+2-2)*(4*m+2-3))+
    (5*(((-4)*m+10)*((4*m+2)*(4*m+2-1)*(4*m+2-2)))+
    (15*(((-6)*m+9)*((4*m+2)*(4*m+2-1)))+
    ((96*(m*m*m)+((-96)*(m*m)+((-94)*m+109)))*(4*m+2)+
    (-10)*((2*m+4)*(2*m+4-1)*(2*m+4-2)*(2*m+4-3))))) =
      8*((2*m+1)*(2*m+1)*(7*(m*m)+(7*m+31))) := by
  have h := cert_int_poly_identity boundaryFourLHS boundaryFourRHS
    boundaryFour_normal (fun _ => m)
  simpa [boundaryFourLHS, boundaryFourRHS, certFalling, certAdd, certMul,
    certNeg, certSub, certConst, certScale, certIntEval, certIntPow,
    Int.sub_eq_add_neg] using h

private def boundaryFiveScaledLHS : RingNormaliser.PolyExpr :=
  let m := RingNormaliser.PolyExpr.var 0
  let S := certAdd (certScale 4 m) (certConst 2)
  let T := certAdd (certScale 2 m) (certConst 4)
  let A := certAdd (certScale (-4) m) (certConst 10)
  let B := certAdd (certScale (-6) m) (certConst 9)
  let P := certAdd (certScale 96 (.pow m 3))
    (certAdd (certScale (-96) (.pow m 2))
      (certAdd (certScale (-94) m) (certConst 109)))
  certAdd (certScale 4 (certFalling S 5))
  (certAdd (certScale 5 (certMul A (certFalling S 4)))
  (certAdd (certScale 20 (certMul B (certFalling S 3)))
  (certAdd (certScale 2 (certMul P (certFalling S 2)))
    (certScale (-8) (certFalling T 5)))))

private def boundaryFiveScaledRHS : RingNormaliser.PolyExpr :=
  let m := RingNormaliser.PolyExpr.var 0
  certScale 4 (certMul (.pow (certAdd (certScale 2 m) (certConst 1)) 2)
    (certAdd (certScale 112 (.pow m 3))
      (certAdd (certScale (-80) (.pow m 2))
        (certAdd (certScale 304 m) (certConst 109)))))

private theorem boundaryFiveScaled_normal :
    RingNormaliser.normalize boundaryFiveScaledLHS =
      RingNormaliser.normalize boundaryFiveScaledRHS := by
  set_option maxRecDepth 10000 in
    decide

private theorem boundaryFive_scaled_factor_identity (m : Int) :
    4*((4*m+2)*(4*m+2-1)*(4*m+2-2)*(4*m+2-3)*(4*m+2-4))+
    (5*(((-4)*m+10)*((4*m+2)*(4*m+2-1)*(4*m+2-2)*(4*m+2-3)))+
    (20*(((-6)*m+9)*((4*m+2)*(4*m+2-1)*(4*m+2-2)))+
    (2*((96*(m*m*m)+((-96)*(m*m)+((-94)*m+109)))*
      ((4*m+2)*(4*m+2-1)))+
    (-8)*((2*m+4)*(2*m+4-1)*(2*m+4-2)*(2*m+4-3)*(2*m+4-4))))) =
      4*((2*m+1)*(2*m+1)*
        (112*(m*m*m)+((-80)*(m*m)+(304*m+109)))) := by
  have h := cert_int_poly_identity boundaryFiveScaledLHS boundaryFiveScaledRHS
    boundaryFiveScaled_normal (fun _ => m)
  simpa [boundaryFiveScaledLHS, boundaryFiveScaledRHS, certFalling, certAdd,
    certMul, certNeg, certSub, certConst, certScale, certIntEval, certIntPow,
    Int.sub_eq_add_neg] using h

private theorem two_choose_two_int (n : Nat) (hn : 2 ≤ n) :
    2*(PNPaths.choose n 2:Int)=
      (n:Int)*((n:Int)-1) := by
  have h := congrArg Int.ofNat (two_choose_two n hn)
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul] at h
  have hn1 : ((n-1:Nat):Int)=(n:Int)-1 := by omega
  rw [hn1] at h
  exact h

private theorem six_choose_three_int (n : Nat) (hn : 3 ≤ n) :
    6*(PNPaths.choose n 3:Int)=
      (n:Int)*((n:Int)-1)*((n:Int)-2) := by
  have h := congrArg Int.ofNat (six_choose_three n hn)
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul] at h
  have hn1 : ((n-1:Nat):Int)=(n:Int)-1 := by omega
  have hn2 : ((n-2:Nat):Int)=(n:Int)-2 := by omega
  rw [hn1,hn2] at h
  exact h

private theorem twentyFour_choose_four_int (n : Nat) (hn : 4 ≤ n) :
    24*(PNPaths.choose n 4:Int)=
      (n:Int)*((n:Int)-1)*((n:Int)-2)*((n:Int)-3) := by
  have h := congrArg Int.ofNat (twentyFour_choose_four n hn)
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul] at h
  have hn1 : ((n-1:Nat):Int)=(n:Int)-1 := by omega
  have hn2 : ((n-2:Nat):Int)=(n:Int)-2 := by omega
  have hn3 : ((n-3:Nat):Int)=(n:Int)-3 := by omega
  rw [hn1,hn2,hn3] at h
  exact h

private theorem oneTwenty_choose_five_int (n : Nat) (hn : 5 ≤ n) :
    120*(PNPaths.choose n 5:Int)=
      (n:Int)*((n:Int)-1)*((n:Int)-2)*((n:Int)-3)*((n:Int)-4) := by
  have h := congrArg Int.ofNat (oneTwenty_choose_five n hn)
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul] at h
  have hn1 : ((n-1:Nat):Int)=(n:Int)-1 := by omega
  have hn2 : ((n-2:Nat):Int)=(n:Int)-2 := by omega
  have hn3 : ((n-3:Nat):Int)=(n:Int)-3 := by omega
  have hn4 : ((n-4:Nat):Int)=(n:Int)-4 := by omega
  rw [hn1,hn2,hn3,hn4] at h
  exact h

/-- Exact first exceptional boundary remainder.  This retains the positive
`b₀` surplus which is essential at `r=4`. -/
theorem throughThreeRemainder30_four (m : Nat) (hm : 2 ≤ m) :
    throughThreeRemainder30 m 4=
      8*((2*(m:Int)+1)*(2*(m:Int)+1))*
        (7*((m:Int)*(m:Int))+7*(m:Int)+31) := by
  let S := 4*m+2
  let T := 2*m+4
  have hS2 := two_choose_two_int S (by dsimp [S]; omega)
  have hS3 := six_choose_three_int S (by dsimp [S]; omega)
  have hS4 := twentyFour_choose_four_int S (by dsimp [S]; omega)
  have hT4 := twentyFour_choose_four_int T (by dsimp [T]; omega)
  have hSi : (S:Int)=4*(m:Int)+2 := by
    dsimp [S]
  have hTi : (T:Int)=2*(m:Int)+4 := by
    dsimp [T]
  rw [hSi] at hS2 hS3 hS4
  rw [hTi] at hT4
  let A : Int := (-4)*(m:Int)+10
  let B : Int := (-6)*(m:Int)+9
  let P : Int := 96*((m:Int)*(m:Int)*(m:Int))+
    ((-96)*((m:Int)*(m:Int))+((-94)*(m:Int)+109))
  have e0 : 120*(PNPaths.choose S 4:Int)=
      5*((4*(m:Int)+2)*(4*(m:Int)+2-1)*(4*(m:Int)+2-2)*
        (4*(m:Int)+2-3)) := by
    calc
      120*(PNPaths.choose S 4:Int)=
          5*(24*(PNPaths.choose S 4:Int)) := by
            rw [show (120:Int)=5*24 by decide]
            ac_rfl
      _=_ := by rw [hS4]
  have e1 : 30*A*(PNPaths.choose S 3:Int)=
      5*(A*((4*(m:Int)+2)*(4*(m:Int)+2-1)*(4*(m:Int)+2-2))) := by
    calc
      30*A*(PNPaths.choose S 3:Int)=
          5*(A*(6*(PNPaths.choose S 3:Int))) := by
            rw [show (30:Int)=5*6 by decide]
            ac_rfl
      _=_ := by rw [hS3]
  have e2 : 30*B*(PNPaths.choose S 2:Int)=
      15*(B*((4*(m:Int)+2)*(4*(m:Int)+2-1))) := by
    calc
      30*B*(PNPaths.choose S 2:Int)=
          15*(B*(2*(PNPaths.choose S 2:Int))) := by
            rw [show (30:Int)=15*2 by decide]
            ac_rfl
      _=_ := by rw [hS2]
  have e3 : P*(PNPaths.choose S 1:Int)=P*(4*(m:Int)+2) := by
    rw [choose_one]
    exact congrArg (fun z : Int => P*z) hSi
  have e4 : (-240)*(PNPaths.choose T 4:Int)=
      (-10)*((2*(m:Int)+4)*(2*(m:Int)+4-1)*(2*(m:Int)+4-2)*
        (2*(m:Int)+4-3)) := by
    calc
      (-240)*(PNPaths.choose T 4:Int)=
          (-10)*(24*(PNPaths.choose T 4:Int)) := by
            rw [show (-240:Int)=(-10)*24 by decide]
            ac_rfl
      _=_ := by rw [hT4]
  have hidx1 : 4-1=3 := by decide
  have hidx2 : 4-2=2 := by decide
  have hidx3 : 4-3=1 := by decide
  calc
    throughThreeRemainder30 m 4=
        120*(PNPaths.choose S 4:Int)+
        30*A*(PNPaths.choose S 3:Int)+
        30*B*(PNPaths.choose S 2:Int)+
        P*(PNPaths.choose S 1:Int)+
        (-240)*(PNPaths.choose T 4:Int) := by
          unfold throughThreeRemainder30
          rw [hidx1,hidx2,hidx3]
    _ = 5*((4*(m:Int)+2)*(4*(m:Int)+2-1)*(4*(m:Int)+2-2)*
          (4*(m:Int)+2-3))+
        (5*(A*((4*(m:Int)+2)*(4*(m:Int)+2-1)*(4*(m:Int)+2-2)))+
        (15*(B*((4*(m:Int)+2)*(4*(m:Int)+2-1)))+
        (P*(4*(m:Int)+2)+
        (-10)*((2*(m:Int)+4)*(2*(m:Int)+4-1)*(2*(m:Int)+4-2)*
          (2*(m:Int)+4-3))))) := by
            rw [e0,e1,e2,e3,e4]
            ac_rfl
    _ = 8*((2*(m:Int)+1)*(2*(m:Int)+1)*
          (7*((m:Int)*(m:Int))+(7*(m:Int)+31))) := by
            dsimp [A,B,P]
            exact boundaryFour_factor_identity (m:Int)
    _ = _ := by
      ac_rfl

private theorem four_mul_five_sum (x₀ x₁ x₂ x₃ x₄ : Int) :
    4*(x₀+x₁+x₂+x₃+x₄)=
      4*x₀+4*x₁+4*x₂+4*x₃+4*x₄ := by
  simp only [Int.mul_add]

/-- Exact second exceptional boundary remainder.  The proof works in a
fourfold clearing so the `C(S,4)` contribution remains division-free, then
cancels the positive integer `4`. -/
theorem throughThreeRemainder30_five (m : Nat) (hm : 2 ≤ m) :
    throughThreeRemainder30 m 5=
      ((2*(m:Int)+1)*(2*(m:Int)+1))*
        (112*((m:Int)*(m:Int)*(m:Int))+
          (-80)*((m:Int)*(m:Int))+304*(m:Int)+109) := by
  let S := 4*m+2
  let T := 2*m+4
  have hS2 := two_choose_two_int S (by dsimp [S]; omega)
  have hS3 := six_choose_three_int S (by dsimp [S]; omega)
  have hS4 := twentyFour_choose_four_int S (by dsimp [S]; omega)
  have hS5 := oneTwenty_choose_five_int S (by dsimp [S]; omega)
  have hT5 := oneTwenty_choose_five_int T (by dsimp [T]; omega)
  have hSi : (S:Int)=4*(m:Int)+2 := by dsimp [S]
  have hTi : (T:Int)=2*(m:Int)+4 := by dsimp [T]
  rw [hSi] at hS2 hS3 hS4 hS5
  rw [hTi] at hT5
  let A : Int := (-4)*(m:Int)+10
  let B : Int := (-6)*(m:Int)+9
  let P : Int := 96*((m:Int)*(m:Int)*(m:Int))+
    ((-96)*((m:Int)*(m:Int))+((-94)*(m:Int)+109))
  let x₀ : Int := 120*(PNPaths.choose S 5:Int)
  let x₁ : Int := 30*A*(PNPaths.choose S 4:Int)
  let x₂ : Int := 30*B*(PNPaths.choose S 3:Int)
  let x₃ : Int := P*(PNPaths.choose S 2:Int)
  let x₄ : Int := (-240)*(PNPaths.choose T 5:Int)
  have e0 : 4*x₀=
      4*((4*(m:Int)+2)*(4*(m:Int)+2-1)*(4*(m:Int)+2-2)*
        (4*(m:Int)+2-3)*(4*(m:Int)+2-4)) := by
    dsimp [x₀]
    rw [hS5]
  have e1 : 4*x₁=
      5*(A*((4*(m:Int)+2)*(4*(m:Int)+2-1)*(4*(m:Int)+2-2)*
        (4*(m:Int)+2-3))) := by
    dsimp [x₁]
    calc
      4*(30*A*(PNPaths.choose S 4:Int))=
          5*(A*(24*(PNPaths.choose S 4:Int))) := by
            rw [show (30:Int)=5*6 by decide, show (24:Int)=4*6 by decide]
            ac_rfl
      _=_ := by rw [hS4]
  have e2 : 4*x₂=
      20*(B*((4*(m:Int)+2)*(4*(m:Int)+2-1)*(4*(m:Int)+2-2))) := by
    dsimp [x₂]
    calc
      4*(30*B*(PNPaths.choose S 3:Int))=
          20*(B*(6*(PNPaths.choose S 3:Int))) := by
            rw [show (30:Int)=5*6 by decide, show (20:Int)=4*5 by decide]
            ac_rfl
      _=_ := by rw [hS3]
  have e3 : 4*x₃=
      2*(P*((4*(m:Int)+2)*(4*(m:Int)+2-1))) := by
    dsimp [x₃]
    calc
      4*(P*(PNPaths.choose S 2:Int))=
          2*(P*(2*(PNPaths.choose S 2:Int))) := by ac_rfl
      _=_ := by rw [hS2]
  have e4 : 4*x₄=
      (-8)*((2*(m:Int)+4)*(2*(m:Int)+4-1)*(2*(m:Int)+4-2)*
        (2*(m:Int)+4-3)*(2*(m:Int)+4-4)) := by
    dsimp [x₄]
    calc
      4*((-240)*(PNPaths.choose T 5:Int))=
          (-8)*(120*(PNPaths.choose T 5:Int)) := by
            rw [show (-240:Int)=(-2)*120 by decide,
              show (-8:Int)=4*(-2) by decide]
            ac_rfl
      _=_ := by rw [hT5]
  have hidx1 : 5-1=4 := by decide
  have hidx2 : 5-2=3 := by decide
  have hidx3 : 5-3=2 := by decide
  have hscaled : 4*throughThreeRemainder30 m 5=
      4*(((2*(m:Int)+1)*(2*(m:Int)+1))*
        (112*((m:Int)*(m:Int)*(m:Int))+
          (-80)*((m:Int)*(m:Int))+304*(m:Int)+109)) := by
    calc
      4*throughThreeRemainder30 m 5=4*(x₀+x₁+x₂+x₃+x₄) := by
        unfold throughThreeRemainder30
        rw [hidx1,hidx2,hidx3]
      _=4*x₀+4*x₁+4*x₂+4*x₃+4*x₄ :=
        four_mul_five_sum x₀ x₁ x₂ x₃ x₄
      _=4*((4*(m:Int)+2)*(4*(m:Int)+2-1)*(4*(m:Int)+2-2)*
          (4*(m:Int)+2-3)*(4*(m:Int)+2-4))+
        (5*(A*((4*(m:Int)+2)*(4*(m:Int)+2-1)*(4*(m:Int)+2-2)*
          (4*(m:Int)+2-3)))+
        (20*(B*((4*(m:Int)+2)*(4*(m:Int)+2-1)*(4*(m:Int)+2-2)))+
        (2*(P*((4*(m:Int)+2)*(4*(m:Int)+2-1)))+
        (-8)*((2*(m:Int)+4)*(2*(m:Int)+4-1)*(2*(m:Int)+4-2)*
          (2*(m:Int)+4-3)*(2*(m:Int)+4-4))))) := by
            rw [e0,e1,e2,e3,e4]
            ac_rfl
      _=4*((2*(m:Int)+1)*(2*(m:Int)+1)*
          (112*((m:Int)*(m:Int)*(m:Int))+
            ((-80)*((m:Int)*(m:Int))+(304*(m:Int)+109)))) := by
              dsimp [A,B,P]
              exact boundaryFive_scaled_factor_identity (m:Int)
      _=_ := by ac_rfl
  have hle := Int.le_of_mul_le_mul_left (Int.le_of_eq hscaled) (by decide)
  have hge := Int.le_of_mul_le_mul_left (Int.le_of_eq hscaled.symm) (by decide)
  exact Int.le_antisymm hle hge

/-- The through-`b₃` signed Pascal elevation is nonnegative on its entire
boundary range.  Coordinates four and five use their exact retained-`b₀`
factorisations; all later coordinates split into the off-diagonal doubling
surplus and the simultaneous adjacent-binomial payment. -/
theorem throughThreeRemainder30_nonnegative (m r : Nat)
    (hm : 2 ≤ m) (hr : 4 ≤ r) (hrS : r ≤ 4*m+2) :
    (0:Int) ≤ throughThreeRemainder30 m r := by
  by_cases h4 : r=4
  · subst r
    rw [throughThreeRemainder30_four m hm]
    have hm0 : (0:Int) ≤ (m:Int) := Int.natCast_nonneg _
    have hs : (0:Int) ≤ (2*(m:Int)+1)*(2*(m:Int)+1) :=
      Int.mul_nonneg (by omega) (by omega)
    have hmm : (0:Int) ≤ (m:Int)*(m:Int) := Int.mul_nonneg hm0 hm0
    have hp : (0:Int) ≤
        7*((m:Int)*(m:Int))+7*(m:Int)+31 := by
      have h7mm := Int.mul_nonneg (by decide : (0:Int)≤7) hmm
      have h7m := Int.mul_nonneg (by decide : (0:Int)≤7) hm0
      omega
    exact Int.mul_nonneg (Int.mul_nonneg (by decide) hs) hp
  · by_cases h5 : r=5
    · subst r
      rw [throughThreeRemainder30_five m hm]
      have hm0 : (0:Int) ≤ (m:Int) := Int.natCast_nonneg _
      have hm2 : (2:Int) ≤ (m:Int) := Int.ofNat_le.mpr hm
      have hs : (0:Int) ≤ (2*(m:Int)+1)*(2*(m:Int)+1) :=
        Int.mul_nonneg (by omega) (by omega)
      have hmm : (0:Int) ≤ (m:Int)*(m:Int) := Int.mul_nonneg hm0 hm0
      have hlin : (0:Int) ≤ 112*(m:Int)-80 := by omega
      have hlead : (0:Int) ≤
          ((m:Int)*(m:Int))*(112*(m:Int)-80) :=
        Int.mul_nonneg hmm hlin
      have hid :
          112*((m:Int)*(m:Int)*(m:Int))+(-80)*((m:Int)*(m:Int))=
            ((m:Int)*(m:Int))*(112*(m:Int)-80) := by
        rw [Int.mul_sub,Int.sub_eq_add_neg]
        simp only [Int.mul_neg,Int.neg_mul]
        ac_rfl
      have h304 : (0:Int) ≤ 304*(m:Int) :=
        Int.mul_nonneg (by decide) hm0
      have hp : (0:Int) ≤
          112*((m:Int)*(m:Int)*(m:Int))+(-80)*((m:Int)*(m:Int))+
            304*(m:Int)+109 := by
        rw [hid]
        omega
      exact Int.mul_nonneg hs hp
    · have hr6 : 6≤r := by omega
      let S := 4*m+2
      let T := 2*m+4
      let C₀ : Int := PNPaths.choose S r
      let C₁ : Int := PNPaths.choose S (r-1)
      let C₂ : Int := PNPaths.choose S (r-2)
      let C₃ : Int := PNPaths.choose S (r-3)
      let E₀ : Int := PNPaths.choose T r
      let P : Int := 96*((m:Int)*(m:Int)*(m:Int))+
        ((-96)*((m:Int)*(m:Int))+((-94)*(m:Int)+109))
      have hadj := throughThree_adjacent_binomial_payment m r hm hr6 hrS
      have hadj' :
          30*((4*(m:Int)+(-10))*C₁+(6*(m:Int)+(-9))*C₂)≤
            P*C₃ := by
        dsimp [C₁,C₂,C₃,P,S]
        exact hadj
      have hA : (-4)*(m:Int)+10=-(4*(m:Int)+(-10)) := by omega
      have hB : (-6)*(m:Int)+9=-(6*(m:Int)+(-9)) := by omega
      let Apos : Int := 4*(m:Int)+(-10)
      let Bpos : Int := 6*(m:Int)+(-9)
      have hn1 : 30*(-Apos)*C₁=-(30*(Apos*C₁)) := by
        rw [Int.mul_neg,Int.neg_mul]
        ac_rfl
      have hn2 : 30*(-Bpos)*C₂=-(30*(Bpos*C₂)) := by
        rw [Int.mul_neg,Int.neg_mul]
        ac_rfl
      have hd : 30*(Apos*C₁+Bpos*C₂)=30*(Apos*C₁)+30*(Bpos*C₂) :=
        Int.mul_add _ _ _
      have hband :
          30*((-4)*(m:Int)+10)*C₁+
            30*((-6)*(m:Int)+9)*C₂+P*C₃=
          P*C₃-30*((4*(m:Int)+(-10))*C₁+
            (6*(m:Int)+(-9))*C₂) := by
        rw [hA,hB]
        change 30*(-Apos)*C₁+30*(-Bpos)*C₂+P*C₃=
          P*C₃-30*(Apos*C₁+Bpos*C₂)
        rw [hn1,hn2,hd,Int.sub_eq_add_neg,Int.neg_add]
        ac_rfl
      have hband0 : (0:Int)≤
          30*((-4)*(m:Int)+10)*C₁+
            30*((-6)*(m:Int)+9)*C₂+P*C₃ := by
        rw [hband]
        omega
      have hoff0 : (0:Int)≤120*C₀+(-240)*E₀ := by
        by_cases hrT : r≤T
        · have hoff := choose_remainder_off_double m r hm hr hrT
          have hoffI := Int.ofNat_le.mpr hoff
          have hoffI' : 2*E₀≤C₀ := by
            dsimp [E₀,C₀,S,T]
            simpa only [Int.ofNat_eq_natCast,Int.natCast_mul] using hoffI
          omega
        · have hz : PNPaths.choose T r=0 :=
            choose_zero_of_lt T r (by omega)
          dsimp [E₀,C₀]
          rw [hz]
          have hC : (0:Int)≤(PNPaths.choose S r:Int) := Int.natCast_nonneg _
          have h120 : (0:Int)≤120*(PNPaths.choose S r:Int) :=
            Int.mul_nonneg (by decide : (0:Int)≤120) hC
          omega
      have hsplit : throughThreeRemainder30 m r=
          (120*C₀+(-240)*E₀)+
          (30*((-4)*(m:Int)+10)*C₁+
            30*((-6)*(m:Int)+9)*C₂+P*C₃) := by
        unfold throughThreeRemainder30
        dsimp [C₀,C₁,C₂,C₃,E₀,P,S,T]
        ac_rfl
      rw [hsplit]
      exact Int.add_nonneg hoff0 hband0

/-! ## Minimal reverse-suffix bulk from deficit four onward -/

/-- Symmetry of the local Pascal coefficient.  The proof is internal to the
same subtraction-free recursion used by `PNPaths.choose`. -/
private theorem choose_symm : ∀ n k : Nat, k ≤ n →
    PNPaths.choose n k = PNPaths.choose n (n-k)
  | 0, 0, _ => rfl
  | 0, _+1, h => by omega
  | n+1, 0, _ => by
      rw [choose_zero]
      have hs : n+1-0=n+1 := by omega
      rw [hs,choose_self]
  | n+1, k+1, h => by
      by_cases heq : k=n
      · subst n
        rw [choose_self]
        have hs : k+1-(k+1)=0 := by omega
        rw [hs,choose_zero]
      · have hk : k<n := by omega
        have hk1 : k+1≤n := by omega
        have hs : n+1-(k+1)=n-k := by omega
        have hspos : 0<n-k := by omega
        have hsucc : n-k=(n-k-1)+1 := by omega
        rw [hs,hsucc,PNPaths.choose,PNPaths.choose]
        have h0 := choose_symm n k (by omega)
        have h1 := choose_symm n (k+1) hk1
        have harg : n-(k+1)=n-k-1 := by omega
        rw [harg] at h1
        rw [h0,h1]
        rw [← hsucc]
        exact Nat.add_comm _ _

/-- Iterated Pascal elevation of an integer sequence in deficit coordinates. -/
private def pascalElevate : Nat → (Nat → Int) → Nat → Int
  | 0, b, r => b r
  | d + 1, b, 0 => pascalElevate d b 0
  | d + 1, b, r + 1 =>
      pascalElevate d b (r + 1) + pascalElevate d b r

private theorem pascalElevate_congr (d : Nat) {a b : Nat → Int}
    (h : ∀ r, a r = b r) (r : Nat) :
    pascalElevate d a r = pascalElevate d b r := by
  induction d generalizing r with
  | zero => exact h r
  | succ d ih =>
      cases r with
      | zero => exact ih 0
      | succ r => simp only [pascalElevate, ih]

private theorem pascalElevate_add (d : Nat) (a b : Nat → Int) (r : Nat) :
    pascalElevate d (fun j => a j + b j) r =
      pascalElevate d a r + pascalElevate d b r := by
  induction d generalizing r with
  | zero => rfl
  | succ d ih =>
      cases r with
      | zero => exact ih 0
      | succ r =>
          simp only [pascalElevate, ih]
          ac_rfl

private theorem pascalElevate_scale (d : Nat) (x : Int)
    (a : Nat → Int) (r : Nat) :
    pascalElevate d (fun j => x * a j) r = x * pascalElevate d a r := by
  induction d generalizing r with
  | zero => rfl
  | succ d ih =>
      cases r with
      | zero => exact ih 0
      | succ r =>
          simp only [pascalElevate, ih, Int.mul_add]

private theorem pascalElevate_nonnegative (d : Nat) (a : Nat → Int)
    (ha : ∀ r, (0 : Int) ≤ a r) (r : Nat) :
    (0 : Int) ≤ pascalElevate d a r := by
  induction d generalizing r with
  | zero => exact ha r
  | succ d ih =>
      cases r with
      | zero => exact ih 0
      | succ r =>
          simp only [pascalElevate]
          exact Int.add_nonneg (ih (r + 1)) (ih r)

private def pointSeq (j : Nat) (x : Int) : Nat → Int :=
  fun r => if r = j then x else 0

private theorem pascalElevate_point (d j r : Nat) (x : Int) :
    pascalElevate d (pointSeq j x) r =
      if j ≤ r then (PNPaths.choose d (r - j) : Int) * x else 0 := by
  induction d generalizing r with
  | zero =>
      by_cases heq : r = j
      · subst r
        simp [pascalElevate, pointSeq, choose_zero]
      · by_cases hjr : j ≤ r
        · have hlt : j < r := by omega
          have hz := choose_zero_of_lt 0 (r - j) (by omega)
          simp [pascalElevate, pointSeq, heq, hjr, hz]
        · simp [pascalElevate, pointSeq, heq, hjr]
  | succ d ih =>
      cases r with
      | zero =>
          by_cases hj : j = 0
          · subst j
            have h0 := ih 0
            simpa [choose_zero] using h0
          · have hj0 : ¬ j ≤ 0 := by omega
            simp [pascalElevate, ih, hj0]
      | succ r =>
          simp only [pascalElevate, ih]
          by_cases hjr : j ≤ r
          · have hjr1 : j ≤ r + 1 := by omega
            have hd : r + 1 - j = (r - j) + 1 := by omega
            simp only [if_pos hjr, if_pos hjr1, hd, PNPaths.choose,
              Int.ofNat_eq_natCast, Int.natCast_add, Int.add_mul]
            ac_rfl
          · by_cases heq : j = r + 1
            · subst j
              rw [if_neg hjr]
              simp [choose_zero]
            · have hjr1 : ¬ j ≤ r + 1 := by omega
              simp [hjr, hjr1]

/-- A reverse-tail row extended by zero beyond its Bernstein degree. -/
private def reverseDeficit (D n c r : Nat) : Int :=
  if r ≤ D then reverseTailCoeff D n (D - r) c else 0

private theorem monoCoeff_degree_bottom (D e : Nat) :
    monoCoeff (D + 1) e 0 = monoCoeff D e 0 := by
  cases e with
  | zero => simp [monoCoeff, choose_zero]
  | succ e => simp [monoCoeff]

private theorem diagCoeff_degree_bottom (D n : Nat) :
    diagCoeff (D + 1) n 0 = diagCoeff D n 0 := by
  simp only [diagCoeff, monoCoeff_degree_bottom]

private theorem offCoeff_degree_bottom (D n : Nat) :
    offCoeff (D + 1) n 0 = offCoeff D n 0 := by
  simp only [offCoeff, monoCoeff_degree_bottom]

private theorem reverseTailCoeff_degree_bottom (D n c : Nat) :
    reverseTailCoeff (D + 1) n 0 c = reverseTailCoeff D n 0 c := by
  induction c generalizing n with
  | zero => simp only [reverseTailCoeff, diagCoeff_degree_bottom]
  | succ c ih =>
      simp only [reverseTailCoeff, diagCoeff_degree_bottom,
        offCoeff_degree_bottom, ih]

/-- One degree elevation is exactly one Pascal step, including the top and
bottom boundary and the zero extension outside the old row. -/
private theorem reverseDeficit_step (D n c r : Nat)
    (hD : 2 * (n + c) * (n + c) + 1 ≤ D) :
    reverseDeficit (D + 1) n c r =
      reverseDeficit D n c r +
        (if r = 0 then 0 else reverseDeficit D n c (r - 1)) := by
  cases r with
  | zero =>
      simp only [reverseDeficit, Nat.zero_le, if_pos, Nat.sub_zero]
      rw [reverseTailCoeff_top (D + 1) n c (by omega)]
      rw [reverseTailCoeff_top D n c hD]
      simp
  | succ r =>
      have hne : r + 1 ≠ 0 := by omega
      simp only [hne, if_false, Nat.add_sub_cancel]
      by_cases hr : r < D
      · have hr1D : r + 1 ≤ D := by omega
        have hrD : r ≤ D := by omega
        have hr1D1 : r + 1 ≤ D + 1 := by omega
        simp only [reverseDeficit, if_pos hr1D1, if_pos hr1D, if_pos hrD]
        exact reverseTailCoeff_deficit_step D n c r hr hD
      · by_cases heq : r = D
        · subst r
          have hDle : D ≤ D := Nat.le_refl _
          have hD1le : D + 1 ≤ D + 1 := Nat.le_refl _
          have hnle : ¬ D + 1 ≤ D := by omega
          simp only [reverseDeficit, if_pos hD1le, if_neg hnle, if_pos hDle,
            Nat.sub_self, Int.zero_add]
          exact reverseTailCoeff_degree_bottom D n c
        · have hlarge : D < r := by omega
          have hn0 : ¬ r + 1 ≤ D + 1 := by omega
          have hn1 : ¬ r + 1 ≤ D := by omega
          have hn2 : ¬ r ≤ D := by omega
          simp [reverseDeficit, hn0, hn1, hn2]

private theorem reverseDeficit_elevate (D n c d r : Nat)
    (hD : 2 * (n + c) * (n + c) + 1 ≤ D) :
    reverseDeficit (D + d) n c r =
      pascalElevate d (reverseDeficit D n c) r := by
  induction d generalizing r with
  | zero => simp [pascalElevate]
  | succ d ih =>
      have hsupp : 2 * (n + c) * (n + c) + 1 ≤ D + d := by omega
      rw [show D + (d + 1) = (D + d) + 1 by omega]
      rw [reverseDeficit_step (D + d) n c r hsupp]
      cases r with
      | zero => simp only [if_pos, ih, pascalElevate, Int.add_zero]
      | succ r =>
          have hne : r + 1 ≠ 0 := by omega
          simp only [hne, if_false, Nat.add_sub_cancel, ih, pascalElevate]

private theorem reverseTailCoeff_append (D n k c : Nat) :
    reverseTailCoeff D n k (c + 1) =
      reverseTailCoeff D n k c - offCoeff D (n + c) k +
        diagCoeff D (n + c + 1) k := by
  induction c generalizing n with
  | zero => simp [reverseTailCoeff]
  | succ c ih =>
      change
        diagCoeff D n k - offCoeff D n k +
            reverseTailCoeff D (n + 1) k (c + 1) =
          (diagCoeff D n k - offCoeff D n k +
              reverseTailCoeff D (n + 1) k c) -
            offCoeff D (n + (c + 1)) k +
              diagCoeff D (n + (c + 1) + 1) k
      rw [ih (n + 1)]
      have hnc : n + 1 + c = n + (c + 1) := by omega
      rw [hnc]
      simp only [Int.sub_eq_add_neg]
      ac_rfl

private theorem terminalDiag_deficit_zero (m r : Nat) (hm : 0 < m)
    (hr : 4 ≤ r) :
    diagCoeff (2 * (m + 1) * (m + 1) + 1) (m + 1)
      ((2 * (m + 1) * (m + 1) + 1) - r) = 0 := by
  let D := 2 * (m + 1) * (m + 1) + 1
  let k := D - r
  have hm2 : 2 ≤ m + 1 := by omega
  have hsq : 4 ≤ (m + 1) * (m + 1) := by
    exact Nat.mul_le_mul hm2 hm2
  have hA : 4 ≤ 2 * (m + 1) * (m + 1) := by
    have h := Nat.mul_le_mul_left 2 hsq
    exact Nat.le_trans (show 4 ≤ 8 by decide) (by
      simpa only [Nat.mul_assoc, Nat.mul_one] using h)
  have h0 : ¬ 2 * (m + 1) * (m + 1) - 2 ≤ k := by
    dsimp [D, k]
    omega
  have h1 : ¬ 2 * (m + 1) * (m + 1) - 1 ≤ k := by
    dsimp [D, k]
    omega
  have h2 : ¬ 2 * (m + 1) * (m + 1) ≤ k := by
    dsimp [D, k]
    omega
  have h3 : ¬ 2 * (m + 1) * (m + 1) + 1 ≤ k := by
    dsimp [D, k]
    omega
  change diagCoeff D (m + 1) k = 0
  simp [diagCoeff, monoCoeff, h0, h1, h2, h3]

private theorem terminalOff_deficit (m r : Nat) (hm : 0 < m) :
    offCoeff (2 * (m + 1) * (m + 1) + 1) m
      ((2 * (m + 1) * (m + 1) + 1) - r) =
        Int.ofNat (8 * m * (m + 1)) *
          (PNPaths.choose (2 * m + 4) r : Int) := by
  let D := 2 * (m + 1) * (m + 1) + 1
  let e := 2 * m * (m + 1) - 1
  let T := 2 * m + 4
  have hepos : 0 < 2 * m * (m + 1) := by
    have hm1 : 0 < m + 1 := by omega
    exact Nat.mul_pos (Nat.mul_pos (by decide) hm) hm1
  have hsplit : D = e + T := by
    dsimp [D, e, T]
    simp only [Nat.mul_add, Nat.add_mul]
    omega
  have he0 : 0 < e := by
    have hm1 : 0 < m + 1 := by omega
    have hprod : 1 ≤ m * (m + 1) := Nat.mul_pos hm hm1
    have htwo : 2 ≤ 2 * m * (m + 1) := by
      have h := Nat.mul_le_mul_left 2 hprod
      simpa only [Nat.mul_assoc, Nat.mul_one] using h
    dsimp [e]
    omega
  change Int.ofNat (8 * m * (m + 1)) *
      monoCoeff D e (D - r) =
        Int.ofNat (8 * m * (m + 1)) * (PNPaths.choose T r : Int)
  rw [hsplit]
  by_cases hrT : r ≤ T
  · have he : e ≤ e + T - r := by omega
    have hDe : e + T - e = T := by omega
    have hke : e + T - r - e = T - r := by omega
    simp only [monoCoeff, if_pos he, hDe, hke]
    rw [choose_symm T r hrT]
    simp only [Int.ofNat_eq_natCast]
  · have hnot : ¬ e ≤ e + T - r := by omega
    have hz := choose_zero_of_lt T r (by omega)
    simp [monoCoeff, hnot, hz]

private def minimalScaled (m r : Nat) : Int :=
  30 * reverseDeficit (2 * m * m + 1) 1 (m - 1) r

private def minimalBulkScaled (m r : Nat) : Int :=
  if 4 ≤ r then minimalScaled m r else 0

private theorem four_point_bulk (b : Nat → Int) (r : Nat) :
    b r = pointSeq 0 (b 0) r + pointSeq 1 (b 1) r +
      pointSeq 2 (b 2) r + pointSeq 3 (b 3) r +
        (if 4 ≤ r then b r else 0) := by
  by_cases h0 : r = 0
  · subst r
    simp [pointSeq]
  · by_cases h1 : r = 1
    · subst r
      simp [pointSeq]
    · by_cases h2 : r = 2
      · subst r
        simp [pointSeq]
      · by_cases h3 : r = 3
        · subst r
          simp [pointSeq]
        · have hr : 4 ≤ r := by omega
          simp [pointSeq, h0, h1, h2, h3, hr]

private theorem pascalElevate_four_point_bulk (d : Nat) (b : Nat → Int)
    (r : Nat) :
    pascalElevate d b r =
      pascalElevate d (pointSeq 0 (b 0)) r +
      pascalElevate d (pointSeq 1 (b 1)) r +
      pascalElevate d (pointSeq 2 (b 2)) r +
      pascalElevate d (pointSeq 3 (b 3)) r +
      pascalElevate d (fun j => if 4 ≤ j then b j else 0) r := by
  rw [pascalElevate_congr d (four_point_bulk b) r]
  simp only [pascalElevate_add]

private theorem minimalScaled_zero (m : Nat) (hm : 0 < m) :
    minimalScaled m 0 = (m : Int) * ((m : Int) + 1) * 120 := by
  have hend : 1 + (m - 1) = m := by omega
  have hD : 2 * (1 + (m - 1)) * (1 + (m - 1)) + 1 ≤
      2 * m * m + 1 := by
    rw [hend]
    exact Nat.le_refl _
  unfold minimalScaled reverseDeficit
  simp only [Nat.zero_le, if_pos, Nat.sub_zero]
  rw [reverseTailCoeff_top (2 * m * m + 1) 1 (m - 1) hD]
  unfold reverseTopFluxNat
  rw [hend]
  simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul]
  have hmcast' : (((m - 1 : Nat) : Int) = (m : Int) - 1) := by omega
  rw [hmcast']
  have hcast1 : (((1 : Nat) : Int) = (1 : Int)) := rfl
  rw [hcast1]
  have hx : (m : Int) - 1 + 1 = (m : Int) := by omega
  rw [hx]
  change 30 * (4 * (2 * 1 * ((m : Int)) +
    ((m : Int) - 1) * ((m : Int)))) = (m : Int) * ((m : Int) + 1) * 120
  simp only [Int.mul_one]
  let x : Int := (m : Int)
  change 30 * (4 * (2 * x + (x - 1) * x)) = x * (x + 1) * 120
  simp only [Int.mul_add, Int.add_mul, Int.sub_eq_add_neg, Int.neg_mul]
  rw [show (120 : Int) = 30 * 4 by decide]
  omega

private theorem minimalScaled_one (m : Nat) (hm : 0 < m) :
    minimalScaled m 1 =
      (m : Int) * ((m : Int) + 1) * (30 * ((-4) * (m : Int) + 10)) := by
  have h1 : 1 ≤ 2 * m * m + 1 := by omega
  unfold minimalScaled reverseDeficit
  rw [if_pos h1]
  have hidx : 2 * m * m + 1 - 1 = 2 * m * m := by omega
  rw [hidx, minimalBase_deficit_one m hm]
  let x : Int := (m : Int)
  have hfac : -(2*x*(x+1)*(2*x-5)) = x*(x+1)*(-(2*(2*x-5))) := by
    have hL : -(2*x*(x+1)*(2*x-5)) =
        (-1)*(2*x*(x+1)*(2*x-5)) := by omega
    have hR : -(2*(2*x-5)) = (-1)*(2*(2*x-5)) := by omega
    rw [hL, hR]
    ac_rfl
  rw [hfac]
  calc
    30 * (x * (x + 1) * (-(2 * (2*x-5)))) =
        x * (x + 1) * (30 * (-(2 * (2*x-5)))) := by ac_rfl
    _ = x * (x + 1) * (30 * ((-4)*x+10)) := by
      congr 1
      omega

private theorem minimalScaled_two (m : Nat) (hm : 0 < m) :
    minimalScaled m 2 =
      (m : Int) * ((m : Int) + 1) * (30 * ((-6) * (m : Int) + 9)) := by
  have h2 : 2 ≤ 2 * m * m + 1 := by
    have hm1 : 1 ≤ m := by omega
    have hsq : 1 ≤ m * m := Nat.mul_pos hm hm
    have htwo : 2 ≤ 2 * m * m := by
      have h := Nat.mul_le_mul_left 2 hsq
      simpa only [Nat.mul_assoc, Nat.mul_one] using h
    omega
  unfold minimalScaled reverseDeficit
  rw [if_pos h2]
  have hidx : 2 * m * m + 1 - 2 = 2 * m * m - 1 := by omega
  rw [hidx, minimalBase_deficit_two m hm]
  let x : Int := (m : Int)
  have hfac : -(3*x*(x+1)*(2*x-3)) = x*(x+1)*(-(3*(2*x-3))) := by
    have hL : -(3*x*(x+1)*(2*x-3)) =
        (-1)*(3*x*(x+1)*(2*x-3)) := by omega
    have hR : -(3*(2*x-3)) = (-1)*(3*(2*x-3)) := by omega
    rw [hL, hR]
    ac_rfl
  rw [hfac]
  calc
    30 * (x * (x + 1) * (-(3 * (2*x-3)))) =
        x * (x + 1) * (30 * (-(3 * (2*x-3)))) := by ac_rfl
    _ = x * (x + 1) * (30 * ((-6)*x+9)) := by
      congr 1
      omega

private theorem minimalScaled_three (m : Nat) (hm : 0 < m) :
    minimalScaled m 3 =
      (m : Int) * ((m : Int) + 1) *
        (96 * ((m : Int) * (m : Int) * (m : Int)) +
          ((-96) * ((m : Int) * (m : Int)) + ((-94) * (m : Int) + 109))) := by
  have h3 : 3 ≤ 2 * m * m + 1 := by
    have hm1 : 1 ≤ m := by omega
    have hsq : 1 ≤ m * m := Nat.mul_pos hm hm
    have htwo : 2 ≤ 2 * m * m := by
      have h := Nat.mul_le_mul_left 2 hsq
      simpa only [Nat.mul_assoc, Nat.mul_one] using h
    omega
  unfold minimalScaled reverseDeficit
  rw [if_pos h3]
  have hidx : 2 * m * m + 1 - 3 = 2 * m * m - 2 := by omega
  rw [hidx, minimalBase_deficit_three m hm]
  dsimp [iPow]
  simp only [Int.sub_eq_add_neg, Int.neg_mul]
  ac_rfl

private def throughThreeBand30 (m r : Nat) : Int :=
  120 * (PNPaths.choose (4*m+2) r : Int) +
  30 * ((-4)*(m:Int)+10) * (PNPaths.choose (4*m+2) (r-1) : Int) +
  30 * ((-6)*(m:Int)+9) * (PNPaths.choose (4*m+2) (r-2) : Int) +
  (96*((m:Int)*(m:Int)*(m:Int))+
    ((-96)*((m:Int)*(m:Int))+((-94)*(m:Int)+109))) *
      (PNPaths.choose (4*m+2) (r-3) : Int)

private theorem minimalScaled_old_elevate (m r : Nat) (hm : 0 < m) :
    30 * reverseDeficit (2 * (m + 1) * (m + 1) + 1) 1 (m - 1) r =
      pascalElevate (4*m+2) (minimalScaled m) r := by
  let D := 2*m*m+1
  let S := 4*m+2
  have hend : 1 + (m - 1) = m := by omega
  have hD : 2 * (1 + (m - 1)) * (1 + (m - 1)) + 1 ≤ D := by
    dsimp [D]
    rw [hend]
    exact Nat.le_refl _
  have hdeg : D + S = 2 * (m + 1) * (m + 1) + 1 := by
    dsimp [D, S]
    simp only [Nat.mul_add, Nat.add_mul]
    omega
  have he := reverseDeficit_elevate D 1 (m - 1) S r hD
  rw [← hdeg]
  rw [he]
  unfold minimalScaled
  rw [pascalElevate_scale]

private theorem pascalElevate_minimal_split (m r : Nat) (hm : 0 < m)
    (hr : 4 ≤ r) :
    pascalElevate (4*m+2) (minimalScaled m) r =
      (m:Int)*((m:Int)+1)*throughThreeBand30 m r +
        pascalElevate (4*m+2) (minimalBulkScaled m) r := by
  rw [pascalElevate_four_point_bulk]
  rw [pascalElevate_point, pascalElevate_point, pascalElevate_point,
    pascalElevate_point]
  simp only [if_pos (show 0 ≤ r by omega), if_pos (show 1 ≤ r by omega),
    if_pos (show 2 ≤ r by omega), if_pos (show 3 ≤ r by omega),
    Nat.sub_zero]
  rw [minimalScaled_zero m hm, minimalScaled_one m hm,
    minimalScaled_two m hm, minimalScaled_three m hm]
  unfold minimalBulkScaled throughThreeBand30
  simp only [Int.mul_add, Int.add_mul]
  ac_rfl

/-- Exact one-scale recurrence after removing the four signed boundary
coordinates.  The remaining old suffix is Pascal-elevated coefficientwise;
the appended cell is paid by the already factored through-`b₃` remainder. -/
theorem minimalScaled_bulk_recurrence (m r : Nat) (hm : 0 < m)
    (hr : 4 ≤ r) (hrD : r ≤ 2 * (m + 1) * (m + 1) + 1) :
    minimalScaled (m + 1) r =
      pascalElevate (4*m+2) (minimalBulkScaled m) r +
        (m:Int)*((m:Int)+1)*throughThreeRemainder30 m r := by
  let D := 2 * (m + 1) * (m + 1) + 1
  have htail : (m + 1) - 1 = m := by omega
  have hold : 1 + (m - 1) = m := by omega
  have hc : (m - 1) + 1 = m := by omega
  unfold minimalScaled reverseDeficit
  rw [if_pos hrD, htail]
  change 30 * reverseTailCoeff D 1 (D-r) m = _
  have happ := reverseTailCoeff_append D 1 (D-r) (m-1)
  rw [hc] at happ
  rw [happ]
  rw [hold]
  rw [terminalDiag_deficit_zero m r hm hr]
  rw [terminalOff_deficit m r hm]
  have helev := minimalScaled_old_elevate m r hm
  have helevD : 30 * reverseDeficit D 1 (m-1) r =
      pascalElevate (4*m+2) (minimalScaled m) r := by
    simpa only [D] using helev
  have hrDef : reverseDeficit D 1 (m-1) r =
      reverseTailCoeff D 1 (D-r) (m-1) := by
    unfold reverseDeficit
    rw [if_pos hrD]
  rw [← hrDef]
  rw [Int.mul_add, Int.mul_sub]
  rw [helevD]
  rw [pascalElevate_minimal_split m r hm hr]
  let E : Int := PNPaths.choose (2*m+4) r
  have hoff : 30 * (Int.ofNat (8*m*(m+1)) * E) =
      (m:Int)*((m:Int)+1)*(240*E) := by
    simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add]
    have h8 : (((8:Nat):Int) = (8:Int)) := rfl
    rw [h8, show (240:Int)=30*8 by decide]
    ac_rfl
  have hrem : throughThreeRemainder30 m r =
      throughThreeBand30 m r + (-240)*E := by
    unfold throughThreeRemainder30 throughThreeBand30
    dsimp [E]
  rw [hoff, hrem]
  have hdist :
      (m:Int)*((m:Int)+1)*(throughThreeBand30 m r+(-240)*E) =
        (m:Int)*((m:Int)+1)*throughThreeBand30 m r+
          (m:Int)*((m:Int)+1)*((-240)*E) := by
    rw [Int.mul_add]
  rw [hdist]
  simp only [Int.mul_zero, Int.add_zero, Int.sub_eq_add_neg]
  have hneg :
      -((m:Int)*((m:Int)+1)*(240*E)) =
        (m:Int)*((m:Int)+1)*((-240)*E) := by
    rw [show (-240:Int)=-(240:Int) by decide]
    simp only [Int.neg_mul, Int.mul_neg]
  rw [hneg]
  ac_rfl

/-! ### The three far-edge coordinates of the through-`b₃` payment -/

private def farThreeLHS : RingNormaliser.PolyExpr :=
  let m := RingNormaliser.PolyExpr.var 0
  certAdd (certScale 96 (.pow m 3))
    (certAdd (certScale (-96) (.pow m 2))
      (certAdd (certScale (-94) m) (certConst 109)))

private def farThreeRHS : RingNormaliser.PolyExpr :=
  let m := RingNormaliser.PolyExpr.var 0
  certAdd
    (certMul (certSub m (certConst 2))
      (certAdd (certScale 96 (.pow m 2))
        (certAdd (certScale 96 m) (certConst 98))))
    (certConst 305)

private theorem farThree_normal :
    RingNormaliser.normalize farThreeLHS =
      RingNormaliser.normalize farThreeRHS := by decide

private theorem farThree_factor_identity (m : Int) :
    96*(m*m*m)+((-96)*(m*m)+((-94)*m+109)) =
      (m-2)*(96*(m*m)+(96*m+98))+305 := by
  have h := cert_int_poly_identity farThreeLHS farThreeRHS farThree_normal
    (fun _ => m)
  simpa [farThreeLHS, farThreeRHS, certAdd, certMul, certNeg, certSub,
    certConst, certScale, certIntEval, certIntPow, Int.sub_eq_add_neg] using h

private def farTwoLHS : RingNormaliser.PolyExpr :=
  let m := RingNormaliser.PolyExpr.var 0
  let S := certAdd (certScale 4 m) (certConst 2)
  let B := certAdd (certScale (-6) m) (certConst 9)
  let P := farThreeLHS
  certAdd (certScale 30 B) (certMul P S)

private def farTwoRHS : RingNormaliser.PolyExpr :=
  let m := RingNormaliser.PolyExpr.var 0
  certAdd
    (certMul (certSub m (certConst 2))
      (certAdd (certScale 384 (.pow m 3))
        (certAdd (certScale 576 (.pow m 2))
          (certAdd (certScale 584 m) (certConst 1236)))))
    (certConst 2960)

private theorem farTwo_normal :
    RingNormaliser.normalize farTwoLHS =
      RingNormaliser.normalize farTwoRHS := by decide

private theorem farTwo_factor_identity (m : Int) :
    30*((-6)*m+9)+
      (96*(m*m*m)+((-96)*(m*m)+((-94)*m+109)))*(4*m+2) =
    (m-2)*(384*(m*m*m)+(576*(m*m)+(584*m+1236)))+2960 := by
  have h := cert_int_poly_identity farTwoLHS farTwoRHS farTwo_normal
    (fun _ => m)
  simpa [farTwoLHS, farTwoRHS, farThreeLHS, certAdd, certMul, certNeg,
    certSub, certConst, certScale, certIntEval, certIntPow,
    Int.sub_eq_add_neg] using h

private def farOneDoubledLHS : RingNormaliser.PolyExpr :=
  let m := RingNormaliser.PolyExpr.var 0
  let S := certAdd (certScale 4 m) (certConst 2)
  let A := certAdd (certScale (-4) m) (certConst 10)
  let B := certAdd (certScale (-6) m) (certConst 9)
  let P := farThreeLHS
  certAdd (certScale 60 A)
    (certAdd (certScale 60 (certMul B S))
      (certMul P (certMul S (certSub S (certConst 1)))))

private def farOneDoubledRHS : RingNormaliser.PolyExpr :=
  let m := RingNormaliser.PolyExpr.var 0
  certAdd
    (certMul (certSub m (certConst 2))
      (certAdd (certScale 1536 (.pow m 4))
        (certAdd (certScale 2688 (.pow m 3))
          (certAdd (certScale 2912 (.pow m 2))
            (certAdd (certScale 4808 m) (certConst 11936))))))
    (certConst 25770)

private theorem farOneDoubled_normal :
    RingNormaliser.normalize farOneDoubledLHS =
      RingNormaliser.normalize farOneDoubledRHS := by decide

private theorem farOneDoubled_factor_identity (m : Int) :
    60*((-4)*m+10)+
      (60*(((-6)*m+9)*(4*m+2))+
        (96*(m*m*m)+((-96)*(m*m)+((-94)*m+109)))*
          ((4*m+2)*(4*m+2-1))) =
    (m-2)*(1536*(m*m*m*m)+(2688*(m*m*m)+(2912*(m*m)+
      (4808*m+11936))))+25770 := by
  have h := cert_int_poly_identity farOneDoubledLHS farOneDoubledRHS
    farOneDoubled_normal (fun _ => m)
  simpa [farOneDoubledLHS, farOneDoubledRHS, farThreeLHS, certAdd,
    certMul, certNeg, certSub, certConst, certScale, certIntEval,
    certIntPow, Int.sub_eq_add_neg] using h

private def boundaryP (m : Nat) : Int :=
  96*((m:Int)*(m:Int)*(m:Int))+
    ((-96)*((m:Int)*(m:Int))+((-94)*(m:Int)+109))

private theorem choose_pred_endpoint (S : Nat) (hS : 0 < S) :
    PNPaths.choose S (S-1) = S := by
  have hform : (S-1)+1=S := by omega
  have h := choose_pred (S-1)
  simpa only [hform] using h

private theorem throughThree_far_three (m : Nat) (hm : 2 ≤ m) :
    throughThreeRemainder30 m ((4*m+2)+3) = boundaryP m := by
  let S := 4*m+2
  let T := 2*m+4
  have hT : T < S+3 := by dsimp [S,T]; omega
  have hzT := choose_zero_of_lt T (S+3) hT
  have hz0 := choose_zero_of_lt S (S+3) (by omega)
  have hz1 := choose_zero_of_lt S (S+2) (by omega)
  have hz2 := choose_zero_of_lt S (S+1) (by omega)
  have hs1 : S+3-1=S+2 := by omega
  have hs2 : S+3-2=S+1 := by omega
  have hs3 : S+3-3=S := by omega
  unfold throughThreeRemainder30
  change 120*(PNPaths.choose S (S+3):Int)+
      30*((-4)*(m:Int)+10)*(PNPaths.choose S (S+3-1):Int)+
      30*((-6)*(m:Int)+9)*(PNPaths.choose S (S+3-2):Int)+
      boundaryP m*(PNPaths.choose S (S+3-3):Int)+
      (-240)*(PNPaths.choose T (S+3):Int)=boundaryP m
  rw [hs1,hs2,hs3,hz0,hz1,hz2,choose_self,hzT]
  simp

private theorem throughThree_far_two (m : Nat) (hm : 2 ≤ m) :
    throughThreeRemainder30 m ((4*m+2)+2) =
      30*((-6)*(m:Int)+9)+boundaryP m*(4*(m:Int)+2) := by
  let S := 4*m+2
  let T := 2*m+4
  have hS : 0<S := by dsimp [S]; omega
  have hT : T < S+2 := by dsimp [S,T]; omega
  have hzT := choose_zero_of_lt T (S+2) hT
  have hz0 := choose_zero_of_lt S (S+2) (by omega)
  have hz1 := choose_zero_of_lt S (S+1) (by omega)
  have hs1 : S+2-1=S+1 := by omega
  have hs2 : S+2-2=S := by omega
  have hs3 : S+2-3=S-1 := by omega
  have hpred := choose_pred_endpoint S hS
  have hScast : (S:Int)=4*(m:Int)+2 := by
    dsimp [S]
  unfold throughThreeRemainder30
  change 120*(PNPaths.choose S (S+2):Int)+
      30*((-4)*(m:Int)+10)*(PNPaths.choose S (S+2-1):Int)+
      30*((-6)*(m:Int)+9)*(PNPaths.choose S (S+2-2):Int)+
      boundaryP m*(PNPaths.choose S (S+2-3):Int)+
      (-240)*(PNPaths.choose T (S+2):Int)=
        30*((-6)*(m:Int)+9)+boundaryP m*(4*(m:Int)+2)
  rw [hs1,hs2,hs3,hz0,hz1,choose_self,hpred,hzT]
  simp only [Int.ofNat_zero,Int.zero_mul,Int.mul_zero,Int.zero_add]
  rw [hScast]
  ac_rfl

private theorem throughThree_far_one_doubled (m : Nat) (hm : 2 ≤ m) :
    2*throughThreeRemainder30 m ((4*m+2)+1) =
      60*((-4)*(m:Int)+10)+
        (60*(((-6)*(m:Int)+9)*(4*(m:Int)+2))+
          boundaryP m*((4*(m:Int)+2)*(4*(m:Int)+2-1))) := by
  let S := 4*m+2
  let T := 2*m+4
  have hS : 2≤S := by dsimp [S]; omega
  have hT : T < S+1 := by dsimp [S,T]; omega
  have hzT := choose_zero_of_lt T (S+1) hT
  have hz0 := choose_zero_of_lt S (S+1) (by omega)
  have hs1 : S+1-1=S := by omega
  have hs2 : S+1-2=S-1 := by omega
  have hs3 : S+1-3=S-2 := by omega
  have hpred := choose_pred_endpoint S (by omega)
  have hsymm : PNPaths.choose S (S-2)=PNPaths.choose S 2 := by
    exact (choose_symm S 2 hS).symm
  have hchoose := two_choose_two_int S hS
  have hScast : (S:Int)=4*(m:Int)+2 := by
    dsimp [S]
  unfold throughThreeRemainder30
  change 2*(120*(PNPaths.choose S (S+1):Int)+
      30*((-4)*(m:Int)+10)*(PNPaths.choose S (S+1-1):Int)+
      30*((-6)*(m:Int)+9)*(PNPaths.choose S (S+1-2):Int)+
      boundaryP m*(PNPaths.choose S (S+1-3):Int)+
      (-240)*(PNPaths.choose T (S+1):Int)) = _
  rw [hs1,hs2,hs3,hz0,choose_self,hpred,hsymm,hzT]
  simp only [Int.ofNat_zero,Int.ofNat_one,Int.zero_mul,Int.mul_zero,
    Int.zero_add,Int.add_zero,Int.mul_one]
  rw [Int.mul_add,Int.mul_add]
  have hPC : 2*(boundaryP m*(PNPaths.choose S 2:Int))=
      boundaryP m*(2*(PNPaths.choose S 2:Int)) := by ac_rfl
  rw [hPC]
  rw [hchoose,hScast]
  simp only [Int.mul_add,Int.add_mul]
  ac_rfl

private theorem boundaryP_nonnegative (m : Nat) (hm : 2 ≤ m) :
    (0:Int) ≤ boundaryP m := by
  unfold boundaryP
  rw [farThree_factor_identity (m:Int)]
  have hm0 : (0:Int)≤(m:Int) := Int.natCast_nonneg _
  have hm2 : (2:Int)≤(m:Int) := Int.ofNat_le.mpr hm
  have hq : (0:Int)≤(m:Int)-2 := by omega
  have hs : (0:Int)≤(m:Int)*(m:Int) := Int.mul_nonneg hm0 hm0
  have h96s : (0:Int)≤96*((m:Int)*(m:Int)) :=
    Int.mul_nonneg (by decide) hs
  have h96m : (0:Int)≤96*(m:Int) := Int.mul_nonneg (by decide) hm0
  have hpoly : (0:Int)≤96*((m:Int)*(m:Int))+(96*(m:Int)+98) := by omega
  exact Int.add_nonneg (Int.mul_nonneg hq hpoly) (by decide)

private theorem throughThree_far_two_nonnegative (m : Nat) (hm : 2 ≤ m) :
    (0:Int)≤throughThreeRemainder30 m ((4*m+2)+2) := by
  rw [throughThree_far_two m hm]
  unfold boundaryP
  rw [farTwo_factor_identity (m:Int)]
  have hm0 : (0:Int)≤(m:Int) := Int.natCast_nonneg _
  have hm2 : (2:Int)≤(m:Int) := Int.ofNat_le.mpr hm
  have hq : (0:Int)≤(m:Int)-2 := by omega
  have hs : (0:Int)≤(m:Int)*(m:Int) := Int.mul_nonneg hm0 hm0
  have hc : (0:Int)≤(m:Int)*(m:Int)*(m:Int) := Int.mul_nonneg hs hm0
  have h384 : (0:Int)≤384*((m:Int)*(m:Int)*(m:Int)) :=
    Int.mul_nonneg (by decide) hc
  have h576 : (0:Int)≤576*((m:Int)*(m:Int)) :=
    Int.mul_nonneg (by decide) hs
  have h584 : (0:Int)≤584*(m:Int) := Int.mul_nonneg (by decide) hm0
  have hpoly : (0:Int)≤384*((m:Int)*(m:Int)*(m:Int))+
      (576*((m:Int)*(m:Int))+(584*(m:Int)+1236)) := by omega
  exact Int.add_nonneg (Int.mul_nonneg hq hpoly) (by decide)

private theorem throughThree_far_one_nonnegative (m : Nat) (hm : 2 ≤ m) :
    (0:Int)≤throughThreeRemainder30 m ((4*m+2)+1) := by
  have hscaled : (0:Int)≤2*throughThreeRemainder30 m ((4*m+2)+1) := by
    rw [throughThree_far_one_doubled m hm]
    unfold boundaryP
    rw [farOneDoubled_factor_identity (m:Int)]
    have hm0 : (0:Int)≤(m:Int) := Int.natCast_nonneg _
    have hm2 : (2:Int)≤(m:Int) := Int.ofNat_le.mpr hm
    have hq : (0:Int)≤(m:Int)-2 := by omega
    have hs : (0:Int)≤(m:Int)*(m:Int) := Int.mul_nonneg hm0 hm0
    have hc : (0:Int)≤(m:Int)*(m:Int)*(m:Int) := Int.mul_nonneg hs hm0
    have hf : (0:Int)≤(m:Int)*(m:Int)*(m:Int)*(m:Int) :=
      Int.mul_nonneg hc hm0
    have h1536 : (0:Int)≤1536*((m:Int)*(m:Int)*(m:Int)*(m:Int)) :=
      Int.mul_nonneg (by decide) hf
    have h2688 : (0:Int)≤2688*((m:Int)*(m:Int)*(m:Int)) :=
      Int.mul_nonneg (by decide) hc
    have h2912 : (0:Int)≤2912*((m:Int)*(m:Int)) :=
      Int.mul_nonneg (by decide) hs
    have h4808 : (0:Int)≤4808*(m:Int) := Int.mul_nonneg (by decide) hm0
    have hpoly : (0:Int)≤1536*((m:Int)*(m:Int)*(m:Int)*(m:Int))+
        (2688*((m:Int)*(m:Int)*(m:Int))+
          (2912*((m:Int)*(m:Int))+(4808*(m:Int)+11936))) := by omega
    exact Int.add_nonneg (Int.mul_nonneg hq hpoly) (by decide)
  exact Int.le_of_mul_le_mul_left hscaled (by decide)

private theorem throughThree_far_zero (m r : Nat) (hm : 2 ≤ m)
    (hr : 4*m+2+4 ≤ r) : throughThreeRemainder30 m r = 0 := by
  have hz0 := choose_zero_of_lt (4*m+2) r (by omega)
  have hz1 := choose_zero_of_lt (4*m+2) (r-1) (by omega)
  have hz2 := choose_zero_of_lt (4*m+2) (r-2) (by omega)
  have hz3 := choose_zero_of_lt (4*m+2) (r-3) (by omega)
  have hzT := choose_zero_of_lt (2*m+4) r (by omega)
  unfold throughThreeRemainder30
  rw [hz0,hz1,hz2,hz3,hzT]
  simp

/-- Full-support version of the through-`b₃` payment.  Beyond the range of
the adjacent-binomial argument there are exactly three nonzero endpoint
coordinates; the reflective factorizations above prove each nonnegative. -/
theorem throughThreeRemainder30_nonnegative_all (m r : Nat)
    (hm : 2 ≤ m) (hr : 4 ≤ r) :
    (0:Int) ≤ throughThreeRemainder30 m r := by
  by_cases hmain : r ≤ 4*m+2
  · exact throughThreeRemainder30_nonnegative m r hm hr hmain
  · by_cases h1 : r=4*m+2+1
    · subst r
      exact throughThree_far_one_nonnegative m hm
    · by_cases h2 : r=4*m+2+2
      · subst r
        exact throughThree_far_two_nonnegative m hm
      · by_cases h3 : r=4*m+2+3
        · subst r
          rw [throughThree_far_three m hm]
          exact boundaryP_nonnegative m hm
        · have hfar : 4*m+2+4≤r := by omega
          rw [throughThree_far_zero m r hm hfar]
          decide

/-- Every supported deficit from four onward in the minimal start-one row is
nonnegative after the harmless positive clearing factor `30`.  The induction
uses the exact one-scale recurrence and no global positivity hypothesis. -/
theorem minimalScaled_bulk_nonnegative (m r : Nat)
    (hm : 2 ≤ m) (hr : 4 ≤ r) (hrD : r ≤ 2*m*m+1) :
    (0:Int) ≤ minimalScaled m r := by
  obtain ⟨q, hmq⟩ := Nat.exists_eq_add_of_le hm
  subst m
  induction q generalizing r with
  | zero =>
      have hcases : r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 ∨ r=9 := by omega
      rcases hcases with h4 | h5 | h6 | h7 | h8 | h9
      · subst r; decide
      · subst r; decide
      · subst r; decide
      · subst r; decide
      · subst r; decide
      · subst r; decide
  | succ q ih =>
      let p := 2+q
      have hp2 : 2≤p := by dsimp [p]; omega
      have hp0 : 0<p := by omega
      have hnext : 2+(q+1)=p+1 := by dsimp [p]; omega
      rw [hnext]
      rw [minimalScaled_bulk_recurrence p r hp0 hr (by simpa [hnext] using hrD)]
      apply Int.add_nonneg
      · apply pascalElevate_nonnegative
        intro j
        unfold minimalBulkScaled
        by_cases hj4 : 4≤j
        · rw [if_pos hj4]
          by_cases hjD : j≤2*p*p+1
          · exact ih j hj4 (by omega) (by simpa [p] using hjD)
          · have hz : minimalScaled p j=0 := by
              unfold minimalScaled reverseDeficit
              rw [if_neg hjD]
              decide
            rw [hz]
            decide
        · rw [if_neg hj4]
          decide
      · have hpI : (0:Int)≤(p:Int) := Int.natCast_nonneg _
        have hp1I : (0:Int)≤(p:Int)+1 := by omega
        have hfac : (0:Int)≤(p:Int)*((p:Int)+1) :=
          Int.mul_nonneg hpI hp1I
        exact Int.mul_nonneg hfac
          (throughThreeRemainder30_nonnegative_all p r hp2 hr)

/-- Concrete unscaled minimal theta-residual suffix: for every terminal cell
`m≥2`, all Bernstein coefficients at deficit at least four are nonnegative. -/
theorem minimalBase_bulk_nonnegative (m r : Nat)
    (hm : 2 ≤ m) (hr : 4 ≤ r) (hrD : r ≤ 2*m*m+1) :
    (0:Int) ≤
      reverseTailCoeff (2*m*m+1) 1 ((2*m*m+1)-r) (m-1) := by
  have hs := minimalScaled_bulk_nonnegative m r hm hr hrD
  unfold minimalScaled reverseDeficit at hs
  rw [if_pos hrD] at hs
  exact Int.le_of_mul_le_mul_left hs (by decide)

end YMGap.Continuum.ThetaResidualPascalTelescope

#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.bernMon_left_extract
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.bernMon_right_extract
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.bernMon_mid_extract
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.bernMon_weighted_midpoint_square
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.bernMon_weighted_midpoint_nonneg
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.prevEdge_one_monomial_obstructed
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.prevEdge_one_monomial_not_nonnegative
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.shiftedTwo_local_four
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.shiftedTwo_local_five_of_first_zero
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.shiftedTwo_nonnegative_obstructed
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.shiftedTwo_signed_cutoff_two_obstructed
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.reverseTopFluxNat_step
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.reverseTailCoeff_top
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.reverseTailCoeff_top_nonnegative
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.reverseTailCoeff_degree_step
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.reverseTailCoeff_deficit_step
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.reverseTailCoeff_deficit_nonnegative
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.reverseTailCoeff_top_one
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.minimalBase_deficit_one
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.minimalBase_deficit_one_negative
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.two_mul_topTwo_cell_drift
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.two_mul_reverseTailCoeff_top_two
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.reverseTopTwoClosed_append
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.startTwoPoly_step
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.topTwo_terminal_pair
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.reverseTopTwoClosed_start_one
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.minimalBase_deficit_two
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.minimalBase_deficit_two_negative
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.six_mul_reverseTailCoeff_top_three
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.reverseTopThreeClosed_append
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.firstCellThreeDrift_eq
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.firstCellThreeDrift_negative
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.choose_top_add_mono
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.choose_top_add_linear
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.startThreePoly5_step
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.topThree_terminal_pair
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.five_reverseTopThreeClosed_start_one
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.minimalBase_deficit_three
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.minimalBase_deficit_three_mul
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.choose_adjacent_cross
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.choose_remainder_off_double
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.throughThree_adjacent_scalar_payment
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.throughThree_adjacent_binomial_payment
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.throughThreeRemainder30_four
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.throughThreeRemainder30_five
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.throughThreeRemainder30_nonnegative
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.minimalScaled_bulk_recurrence
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.throughThreeRemainder30_nonnegative_all
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.minimalScaled_bulk_nonnegative
#print axioms YMGap.Continuum.ThetaResidualPascalTelescope.minimalBase_bulk_nonnegative
