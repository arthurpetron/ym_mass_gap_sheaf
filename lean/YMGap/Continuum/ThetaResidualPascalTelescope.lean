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
