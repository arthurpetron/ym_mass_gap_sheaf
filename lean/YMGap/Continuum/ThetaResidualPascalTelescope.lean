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
