/-
Row-wise high-mode coefficient certificate.

The direct bivariate normalizer builds a large table that is too deep for the
ordinary compiler stack.  We first normalize only in the slack variable `Z`,
leaving `M`-polynomials as coefficients, then use a proved dense univariate
convolution on each of the 37 rows separately.  A simultaneous support check
ensures that this specialized row path never discards another variable.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRows

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

open YMGap.Constructive
open YMGap.Continuum.CoreBResidualSimplex
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate

abbrev PE := RingNormaliser.PolyExpr

private def zAdd : List PE → List PE → List PE
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => .add a b :: zAdd p q

private def zScale (a : PE) : List PE → List PE
  | [] => []
  | b :: q => .mul a b :: zScale a q

private def zShift : List PE → List PE
  | [] => []
  | q => .const 0 :: q

private def zMul : List PE → List PE → List PE
  | [], _ => []
  | a :: p, q => zAdd (zScale a q) (zShift (zMul p q))

private def zNeg : List PE → List PE
  | [] => []
  | a :: p => .neg a :: zNeg p

private def zPow (p : List PE) : Nat → List PE
  | 0 => [.const 1]
  | n + 1 => zMul (zPow p n) p

/-- Normalize a polynomial expression only with respect to variable `1`
(the slack `Z`).  Every other variable remains inside the coefficient PE. -/
def zRows : PE → List PE
  | .const c => [.const c]
  | .var i => if i = 1 then [.const 0, .const 1] else [.var i]
  | .add a b => zAdd (zRows a) (zRows b)
  | .mul a b => zMul (zRows a) (zRows b)
  | .neg a => zNeg (zRows a)
  | .pow a n => zPow (zRows a) n

local infix:50 " ≈ " => Q'.eqv

private def evalRows (rho : Nat → Q') (z : Q') : List PE → Q'
  | [] => 0
  | a :: p => RingNormaliser.eval rho a + z * evalRows rho z p

private theorem add_congr₂ {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a + b ≈ a' + b' :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ ha)
    (Q'.add_eqv_congr_left _ _ _ hb)

private theorem mul_congr₂ {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem mul_zero_eqv (a : Q') : a * 0 ≈ 0 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv a 0)
    (RingNormaliser.q_zero_mul a)

private theorem mul_swap_first (a b c : Q') : a * (b * c) ≈ b * (a * c) := by
  refine Q'.eqv_trans _ ((a * b) * c) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  refine Q'.eqv_trans _ ((b * a) * c) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv a b)) ?_
  exact Q'.mul_assoc_eqv b a c

/-! ## Dense one-variable row certificates

Once `zRows` has extracted a coefficient of the slack variable `Z`, the
remaining expression is a polynomial in variable zero (`M`) alone.  Sending
that expression back through the generic sparse normalizer is needlessly
expensive: its canonical insertion sort rebuilds a large intermediate term
list even though the final row is dense and has degree at most seventy-eight.

The following small convolution algebra records a row directly as its list
of `M`-coefficients.  `mOnly` is checked together with nonnegativity, so the
fast path cannot silently discard another variable.  The semantic lemmas
below prove that this exact dense computation evaluates to the original
`PolyExpr`; it is not an external or approximate certificate. -/

abbrev DenseMRow := List Int

private def mRowAdd : DenseMRow → DenseMRow → DenseMRow
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: mRowAdd p q

private def mRowScale (a : Int) : DenseMRow → DenseMRow
  | [] => []
  | b :: q => (a * b) :: mRowScale a q

private def mRowShift : DenseMRow → DenseMRow
  | [] => []
  | q => 0 :: q

private def mRowMul : DenseMRow → DenseMRow → DenseMRow
  | [], _ => []
  | a :: p, q => mRowAdd (mRowScale a q) (mRowShift (mRowMul p q))

private def mRowNeg : DenseMRow → DenseMRow
  | [] => []
  | a :: p => (-a) :: mRowNeg p

private def mRowPow (p : DenseMRow) : Nat → DenseMRow
  | 0 => [1]
  | n + 1 => mRowMul (mRowPow p n) p

/-- Dense expansion in variable zero.  Values of unsupported variables are
irrelevant because `mOnly` is a simultaneous part of `highRowPred`. -/
def mDense : PE → DenseMRow
  | .const c => [c]
  | .var i => if i = 0 then [0, 1] else []
  | .add a b => mRowAdd (mDense a) (mDense b)
  | .mul a b => mRowMul (mDense a) (mDense b)
  | .neg a => mRowNeg (mDense a)
  | .pow a n => mRowPow (mDense a) n

/-- Syntactic support check required by the dense row expansion. -/
def mOnly : PE → Bool
  | .const _ => true
  | .var i => decide (i = 0)
  | .add a b => mOnly a && mOnly b
  | .mul a b => mOnly a && mOnly b
  | .neg a => mOnly a
  | .pow a _ => mOnly a

def denseMRowNonnegative : DenseMRow → Bool
  | [] => true
  | a :: p => decide ((0 : Int) ≤ a) && denseMRowNonnegative p

theorem denseMRowNonnegative_append : ∀ p q,
    denseMRowNonnegative (p ++ q) =
      (denseMRowNonnegative p && denseMRowNonnegative q)
  | [], _ => rfl
  | _ :: p, q => by
      simp only [List.cons_append, denseMRowNonnegative]
      rw [denseMRowNonnegative_append p q, Bool.and_assoc]

theorem denseMRowNonnegative_of_take_and_drop {p : DenseMRow} (n : Nat)
    (hhead : denseMRowNonnegative (p.take n) = true)
    (htail : denseMRowNonnegative (p.drop n) = true) :
    denseMRowNonnegative p = true := by
  rw [← List.take_append_drop n p, denseMRowNonnegative_append, hhead, htail]
  rfl

private def evalMRow (M : Q') : DenseMRow → Q'
  | [] => 0
  | a :: p => Q'.ofInt a + M * evalMRow M p

private theorem ofInt_neg (a : Int) : Q'.ofInt (-a) ≈ -(Q'.ofInt a) := by
  show (-a) * (1 : Int) = (-a) * (1 : Int)
  rfl

private theorem evalMRow_add (M : Q') : ∀ p q,
    evalMRow M (mRowAdd p q) ≈ evalMRow M p + evalMRow M q
  | [], q => Q'.eqv_symm (RingNormaliser.eqv_of_eq (Q'.zero_add' _))
  | _ :: _, [] => Q'.eqv_symm (RingNormaliser.eqv_of_eq (Q'.add_zero' _))
  | a :: p, b :: q => by
      refine Q'.eqv_trans _
        ((Q'.ofInt a + Q'.ofInt b) +
          M * (evalMRow M p + evalMRow M q)) _ ?_ ?_
      · exact add_congr₂ (RingNormaliser.ofInt_add a b)
          (Q'.mul_eqv_congr_left M _ _ (evalMRow_add M p q))
      refine Q'.eqv_trans _
        ((Q'.ofInt a + Q'.ofInt b) +
          (M * evalMRow M p + M * evalMRow M q)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.mul_add_eqv M (evalMRow M p) (evalMRow M q))
      exact Q'.add_swap_inner _ _ _ _

private theorem evalMRow_scale (M : Q') (a : Int) : ∀ p,
    evalMRow M (mRowScale a p) ≈ Q'.ofInt a * evalMRow M p
  | [] => Q'.eqv_symm (mul_zero_eqv _)
  | b :: p => by
      refine Q'.eqv_trans _
        (Q'.ofInt a * Q'.ofInt b +
          M * (Q'.ofInt a * evalMRow M p)) _ ?_ ?_
      · exact add_congr₂ (RingNormaliser.ofInt_mul a b)
          (Q'.mul_eqv_congr_left M _ _ (evalMRow_scale M a p))
      refine Q'.eqv_trans _
        (Q'.ofInt a * Q'.ofInt b +
          Q'.ofInt a * (M * evalMRow M p)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (mul_swap_first M (Q'.ofInt a) (evalMRow M p))
      exact Q'.eqv_symm (Q'.mul_add_eqv _ _ _)

private theorem evalMRow_shift (M : Q') : ∀ p,
    evalMRow M (mRowShift p) ≈ M * evalMRow M p
  | [] => Q'.eqv_symm (mul_zero_eqv M)
  | _ :: _ => RingNormaliser.eqv_of_eq (Q'.zero_add' _)

private theorem evalMRow_mul (M : Q') : ∀ p q,
    evalMRow M (mRowMul p q) ≈ evalMRow M p * evalMRow M q
  | [], q => Q'.eqv_symm (RingNormaliser.q_zero_mul (evalMRow M q))
  | a :: p, q => by
      refine Q'.eqv_trans _
        (evalMRow M (mRowScale a q) + evalMRow M (mRowShift (mRowMul p q))) _
        (evalMRow_add M _ _) ?_
      refine Q'.eqv_trans _
        (Q'.ofInt a * evalMRow M q + M * evalMRow M (mRowMul p q)) _ ?_ ?_
      · exact add_congr₂ (evalMRow_scale M a q) (evalMRow_shift M (mRowMul p q))
      refine Q'.eqv_trans _
        (Q'.ofInt a * evalMRow M q + M * (evalMRow M p * evalMRow M q)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left M _ _ (evalMRow_mul M p q))
      refine Q'.eqv_trans _
        (Q'.ofInt a * evalMRow M q + (M * evalMRow M p) * evalMRow M q) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv M (evalMRow M p) (evalMRow M q)))
      exact Q'.eqv_symm (RingNormaliser.q_add_mul _ _ _)

private theorem evalMRow_neg (M : Q') : ∀ p,
    evalMRow M (mRowNeg p) ≈ -(evalMRow M p)
  | [] => RingNormaliser.eqv_of_eq rfl
  | a :: p => by
      refine Q'.eqv_trans _
        (-(Q'.ofInt a) + M * (-(evalMRow M p))) _ ?_ ?_
      · exact add_congr₂ (ofInt_neg a)
          (Q'.mul_eqv_congr_left M _ _ (evalMRow_neg M p))
      refine Q'.eqv_trans _
        (-(Q'.ofInt a) + -(M * evalMRow M p)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv M (evalMRow M p))
      exact Q'.eqv_symm (Q'.neg_add_eqv_split (Q'.ofInt a) (M * evalMRow M p))

private theorem evalMRow_pow (M : Q') (p : DenseMRow) : ∀ n,
    evalMRow M (mRowPow p n) ≈ RingNormaliser.qpow (evalMRow M p) n
  | 0 => by
      refine Q'.eqv_trans _ ((1 : Q') + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr_left 1 _ 0 (mul_zero_eqv M)
      exact RingNormaliser.eqv_of_eq (Q'.add_zero' 1)
  | n + 1 => by
      refine Q'.eqv_trans _
        (evalMRow M (mRowPow p n) * evalMRow M p) _
        (evalMRow_mul M _ _) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (evalMRow_pow M p n)

private theorem evalMRow_mDense (rho : Nat → Q') : ∀ e,
    mOnly e = true →
      evalMRow (rho 0) (mDense e) ≈ RingNormaliser.eval rho e
  | .const c, _ => by
      change Q'.ofInt c + rho 0 * 0 ≈ Q'.ofInt c
      refine Q'.eqv_trans _ (Q'.ofInt c + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ 0 (mul_zero_eqv (rho 0))
      exact RingNormaliser.eqv_of_eq (Q'.add_zero' _)
  | .var i, hi => by
      change decide (i = 0) = true at hi
      have hi' : i = 0 := of_decide_eq_true hi
      subst i
      change 0 + rho 0 * (1 + rho 0 * 0) ≈ rho 0
      refine Q'.eqv_trans _ (0 + rho 0 * (1 + 0)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left 0 _ _
          (Q'.mul_eqv_congr_left (rho 0) _ _
            (Q'.add_eqv_congr_left 1 _ 0 (mul_zero_eqv (rho 0))))
      rw [Q'.add_zero' 1]
      refine Q'.eqv_trans _ (0 + rho 0) _ ?_ ?_
      · exact Q'.add_eqv_congr_left 0 _ _ (Q'.mul_one_eqv (rho 0))
      exact RingNormaliser.eqv_of_eq (Q'.zero_add' _)
  | .add a b, hab => by
      have hs := (Bool.and_eq_true _ _).mp hab
      refine Q'.eqv_trans _
        (evalMRow (rho 0) (mDense a) + evalMRow (rho 0) (mDense b)) _
        (evalMRow_add (rho 0) _ _) ?_
      exact add_congr₂ (evalMRow_mDense rho a hs.1) (evalMRow_mDense rho b hs.2)
  | .mul a b, hab => by
      have hs := (Bool.and_eq_true _ _).mp hab
      refine Q'.eqv_trans _
        (evalMRow (rho 0) (mDense a) * evalMRow (rho 0) (mDense b)) _
        (evalMRow_mul (rho 0) _ _) ?_
      exact mul_congr₂ (evalMRow_mDense rho a hs.1) (evalMRow_mDense rho b hs.2)
  | .neg a, ha => by
      refine Q'.eqv_trans _ (-(evalMRow (rho 0) (mDense a))) _
        (evalMRow_neg (rho 0) _) ?_
      exact Q'.neg_eqv_congr _ _ (evalMRow_mDense rho a ha)
  | .pow a n, ha => by
      refine Q'.eqv_trans _
        (RingNormaliser.qpow (evalMRow (rho 0) (mDense a)) n) _
        (evalMRow_pow (rho 0) _ n) ?_
      exact RingNormaliser.qpow_eqv_congr (evalMRow_mDense rho a ha) n

private theorem ofInt_nonnegative {a : Int} (ha : (0 : Int) ≤ a) :
    (0 : Q') ≤ Q'.ofInt a := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact ha

private theorem evalMRow_nonnegative (M : Q') (hM : (0 : Q') ≤ M) :
    ∀ p, denseMRowNonnegative p = true → (0 : Q') ≤ evalMRow M p
  | [], _ => Q'.le_refl' 0
  | a :: p, hp => by
      have hs : decide ((0 : Int) ≤ a) = true ∧ denseMRowNonnegative p = true := by
        simpa [denseMRowNonnegative] using hp
      exact Q'.zero_le_add _ _
        (ofInt_nonnegative (of_decide_eq_true hs.1))
        (Q'.mul_nonneg _ _ hM (evalMRow_nonnegative M hM p hs.2))

/-- The exact, kernel-decidable row predicate.  Both univariate support and
coefficientwise nonnegativity are checked. -/
def highRowPred (row : PE) : Bool :=
  mOnly row && denseMRowNonnegative (mDense row)

private theorem all_highRowPred_of_support_and_dense : ∀ rows : List PE,
    rows.all mOnly = true →
    denseMRowNonnegative (rows.flatMap mDense) = true →
    rows.all highRowPred = true
  | [], _, _ => rfl
  | row :: rows, hsupport, hdense => by
      have hs : mOnly row = true ∧ rows.all mOnly = true := by
        simpa using hsupport
      have hc : denseMRowNonnegative (mDense row) = true ∧
          denseMRowNonnegative (rows.flatMap mDense) = true := by
        change denseMRowNonnegative
          (mDense row ++ rows.flatMap mDense) = true at hdense
        rw [denseMRowNonnegative_append] at hdense
        exact (Bool.and_eq_true _ _).mp hdense
      have htail := all_highRowPred_of_support_and_dense rows hs.2 hc.2
      simpa [highRowPred, hs.1, hc.1] using htail

private theorem eval_nonnegative_of_highRowPred
    (rho : Nat → Q') (hrho : ∀ i, (0 : Q') ≤ rho i) (row : PE)
    (hrow : highRowPred row = true) :
    (0 : Q') ≤ RingNormaliser.eval rho row := by
  have hs := (Bool.and_eq_true _ _).mp hrow
  have hdense : (0 : Q') ≤ evalMRow (rho 0) (mDense row) :=
    evalMRow_nonnegative (rho 0) (hrho 0) _ hs.2
  exact Q'.le_trans' _ _ _ hdense
    (Q'.le_of_eqv (evalMRow_mDense rho row hs.1))

private theorem evalRows_zAdd (rho : Nat → Q') (z : Q') : ∀ p q,
    evalRows rho z (zAdd p q) ≈ evalRows rho z p + evalRows rho z q
  | [], q => Q'.eqv_symm (RingNormaliser.eqv_of_eq (Q'.zero_add' _))
  | _ :: _, [] => Q'.eqv_symm (RingNormaliser.eqv_of_eq (Q'.add_zero' _))
  | a :: p, b :: q => by
      refine Q'.eqv_trans _
        ((RingNormaliser.eval rho a + RingNormaliser.eval rho b) +
          z * (evalRows rho z p + evalRows rho z q)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left z _ _ (evalRows_zAdd rho z p q))
      refine Q'.eqv_trans _
        ((RingNormaliser.eval rho a + RingNormaliser.eval rho b) +
          (z * evalRows rho z p + z * evalRows rho z q)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.mul_add_eqv z (evalRows rho z p) (evalRows rho z q))
      exact Q'.add_swap_inner _ _ _ _

private theorem evalRows_zScale (rho : Nat → Q') (z : Q') (a : PE) : ∀ p,
    evalRows rho z (zScale a p) ≈
      RingNormaliser.eval rho a * evalRows rho z p
  | [] => Q'.eqv_symm (mul_zero_eqv _)
  | b :: p => by
      refine Q'.eqv_trans _
        (RingNormaliser.eval rho a * RingNormaliser.eval rho b +
          z * (RingNormaliser.eval rho a * evalRows rho z p)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left z _ _ (evalRows_zScale rho z a p))
      refine Q'.eqv_trans _
        (RingNormaliser.eval rho a * RingNormaliser.eval rho b +
          RingNormaliser.eval rho a * (z * evalRows rho z p)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (mul_swap_first z (RingNormaliser.eval rho a) (evalRows rho z p))
      exact Q'.eqv_symm (Q'.mul_add_eqv _ _ _)

private theorem evalRows_zShift (rho : Nat → Q') (z : Q') : ∀ p,
    evalRows rho z (zShift p) ≈ z * evalRows rho z p
  | [] => Q'.eqv_symm (mul_zero_eqv z)
  | _ :: _ => RingNormaliser.eqv_of_eq (Q'.zero_add' _)

private theorem evalRows_zMul (rho : Nat → Q') (z : Q') : ∀ p q,
    evalRows rho z (zMul p q) ≈ evalRows rho z p * evalRows rho z q
  | [], q => Q'.eqv_symm (RingNormaliser.q_zero_mul (evalRows rho z q))
  | a :: p, q => by
      refine Q'.eqv_trans _
        (evalRows rho z (zScale a q) +
          evalRows rho z (zShift (zMul p q))) _
        (evalRows_zAdd rho z _ _) ?_
      refine Q'.eqv_trans _
        (RingNormaliser.eval rho a * evalRows rho z q +
          z * evalRows rho z (zMul p q)) _ ?_ ?_
      · exact add_congr₂ (evalRows_zScale rho z a q)
          (evalRows_zShift rho z (zMul p q))
      refine Q'.eqv_trans _
        (RingNormaliser.eval rho a * evalRows rho z q +
          z * (evalRows rho z p * evalRows rho z q)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left z _ _ (evalRows_zMul rho z p q))
      refine Q'.eqv_trans _
        (RingNormaliser.eval rho a * evalRows rho z q +
          (z * evalRows rho z p) * evalRows rho z q) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv z (evalRows rho z p) (evalRows rho z q)))
      exact Q'.eqv_symm (RingNormaliser.q_add_mul _ _ _)

private theorem evalRows_zNeg (rho : Nat → Q') (z : Q') : ∀ p,
    evalRows rho z (zNeg p) ≈ -(evalRows rho z p)
  | [] => RingNormaliser.eqv_of_eq rfl
  | a :: p => by
      refine Q'.eqv_trans _
        (-RingNormaliser.eval rho a + z * (-(evalRows rho z p))) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left z _ _ (evalRows_zNeg rho z p))
      refine Q'.eqv_trans _
        (-RingNormaliser.eval rho a + -(z * evalRows rho z p)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.mul_neg_eqv z (evalRows rho z p))
      exact Q'.eqv_symm
        (Q'.neg_add_eqv_split
          (RingNormaliser.eval rho a) (z * evalRows rho z p))

private theorem evalRows_zPow (rho : Nat → Q') (z : Q') (p : List PE) : ∀ n,
    evalRows rho z (zPow p n) ≈ RingNormaliser.qpow (evalRows rho z p) n
  | 0 => by
      refine Q'.eqv_trans _ ((1 : Q') + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr_left 1 _ 0 (mul_zero_eqv z)
      exact RingNormaliser.eqv_of_eq (Q'.add_zero' 1)
  | n + 1 => by
      refine Q'.eqv_trans _
        (evalRows rho z (zPow p n) * evalRows rho z p) _
        (evalRows_zMul rho z _ _) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (evalRows_zPow rho z p n)

private theorem evalRows_zRows (rho : Nat → Q') : ∀ e,
    evalRows rho (rho 1) (zRows e) ≈ RingNormaliser.eval rho e
  | .const c => by
      refine Q'.eqv_trans _ (Q'.ofInt c + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ 0 (mul_zero_eqv (rho 1))
      exact RingNormaliser.eqv_of_eq (Q'.add_zero' _)
  | .var i => by
      by_cases hi : i = 1
      · rw [hi]
        change (0 + rho 1 * (1 + rho 1 * 0)) ≈ rho 1
        refine Q'.eqv_trans _ (0 + rho 1 * (1 + 0)) _ ?_ ?_
        · exact Q'.add_eqv_congr_left 0 _ _
            (Q'.mul_eqv_congr_left (rho 1) _ _
              (Q'.add_eqv_congr_left 1 _ 0 (mul_zero_eqv (rho 1))))
        rw [Q'.add_zero' 1]
        refine Q'.eqv_trans _ (0 + rho 1) _ ?_ ?_
        · exact Q'.add_eqv_congr_left 0 _ _ (Q'.mul_one_eqv (rho 1))
        exact RingNormaliser.eqv_of_eq (Q'.zero_add' _)
      · rw [zRows, if_neg hi]
        change rho i + rho 1 * 0 ≈ rho i
        refine Q'.eqv_trans _ (rho i + 0) _ ?_ ?_
        · exact Q'.add_eqv_congr_left _ _ 0 (mul_zero_eqv (rho 1))
        exact RingNormaliser.eqv_of_eq (Q'.add_zero' _)
  | .add a b => by
      refine Q'.eqv_trans _
        (evalRows rho (rho 1) (zRows a) + evalRows rho (rho 1) (zRows b)) _
        (evalRows_zAdd rho (rho 1) _ _) ?_
      exact add_congr₂ (evalRows_zRows rho a) (evalRows_zRows rho b)
  | .mul a b => by
      refine Q'.eqv_trans _
        (evalRows rho (rho 1) (zRows a) * evalRows rho (rho 1) (zRows b)) _
        (evalRows_zMul rho (rho 1) _ _) ?_
      exact mul_congr₂ (evalRows_zRows rho a) (evalRows_zRows rho b)
  | .neg a => by
      refine Q'.eqv_trans _ (-(evalRows rho (rho 1) (zRows a))) _
        (evalRows_zNeg rho (rho 1) _) ?_
      exact Q'.neg_eqv_congr _ _ (evalRows_zRows rho a)
  | .pow a n => by
      refine Q'.eqv_trans _
        (RingNormaliser.qpow (evalRows rho (rho 1) (zRows a)) n) _
        (evalRows_zPow rho (rho 1) _ _) ?_
      exact RingNormaliser.qpow_eqv_congr (evalRows_zRows rho a) n

private theorem evalRows_nonnegative (rho : Nat → Q')
    (hrho : ∀ i, (0 : Q') ≤ rho i) (z : Q') (hz : (0 : Q') ≤ z) :
    ∀ rows : List PE,
      rows.all highRowPred = true →
      (0 : Q') ≤ evalRows rho z rows
  | [], _ => Q'.le_refl' 0
  | row :: rows, hrows => by
      have hs :
          highRowPred row = true ∧ rows.all highRowPred = true := by
        simpa using hrows
      exact Q'.zero_le_add _ _
        (eval_nonnegative_of_highRowPred rho hrho row hs.1)
        (Q'.mul_nonneg _ _ hz
          (evalRows_nonnegative rho hrho z hz rows hs.2))

/-- The two-variable evaluation environment for the high-mode substitution:
variable zero is the nonnegative mode slack `M`, and variable one is the
nonnegative square-root slack `Z`. -/
def highEnvironment (M Z : Q') (i : Nat) : Q' :=
  if i = 0 then M else if i = 1 then Z else 0

/-- The high numerator has slack degree thirty-six. -/
theorem pExactLowerHigh_rows_length :
    (zRows pExactLowerHigh).length = 37 := by decide

/-- The complete list of `Z` rows.  It is public so that independent modules
can kernel-check disjoint chunks and Lake can cache them separately. -/
def highRows : List PE := zRows pExactLowerHigh

/-- Drop five more rows at each step.  The final certificate uses tails zero
through eight, so no single module has to normalize the entire table. -/
def highRowsTail : Nat → List PE
  | 0 => highRows
  | n + 1 => (highRowsTail n).drop 5

/-- A five-row block and its successive one-row tails.  These definitions
support a finer certificate split for any block whose coefficient check is too
dense to check monolithically. -/
def highRowsBlock (n : Nat) : List PE := (highRowsTail n).take 5

def highRowsBlockTail (block : Nat) : Nat → List PE
  | 0 => highRowsBlock block
  | n + 1 => (highRowsBlockTail block n).drop 1

/-- Support half of a singleton row certificate. -/
def highRowSupport (block row : Nat) : Bool :=
  ((highRowsBlockTail block row).take 1).all mOnly

/-- Concatenate the dense `M`-coefficient lists in a singleton row.  The
definition also behaves correctly for an out-of-range empty singleton. -/
def highRowDenseCoefficients (block row : Nat) : DenseMRow :=
  ((highRowsBlockTail block row).take 1).flatMap mDense

def highRowDenseCoefficientTail (block row start : Nat) : DenseMRow :=
  (highRowDenseCoefficients block row).drop start

def highRowDenseCoefficientSlice
    (block row start count : Nat) : DenseMRow :=
  (highRowDenseCoefficientTail block row start).take count

theorem highRowDenseCoefficientTail_nonnegative_of_slice
    (block row start count : Nat)
    (hslice : denseMRowNonnegative
      (highRowDenseCoefficientSlice block row start count) = true)
    (htail : denseMRowNonnegative
      (highRowDenseCoefficientTail block row (start + count)) = true) :
    denseMRowNonnegative
      (highRowDenseCoefficientTail block row start) = true := by
  apply denseMRowNonnegative_of_take_and_drop count hslice
  simpa [highRowDenseCoefficientTail, List.drop_drop] using htail

theorem highRow_certificate_of_support_and_dense
    (block row : Nat)
    (hsupport : highRowSupport block row = true)
    (hdense : denseMRowNonnegative
      (highRowDenseCoefficients block row) = true) :
    ((highRowsBlockTail block row).take 1).all highRowPred = true := by
  apply all_highRowPred_of_support_and_dense
  · exact hsupport
  · exact hdense

/-- A reusable, cost-balanced certificate schedule.  Canonical monomials are
ordered by increasing `M`-exponent, while the shift `N=M+8` makes the early
coefficients the arithmetically largest.  We therefore check widths
`6, 10, 14, 20`, followed by the (higher-exponent) suffix, instead of splitting
merely by coefficient count.  The maximum possible row degree is seventy-eight,
so the final suffix contains at most twenty-nine, substantially smaller,
coefficients. -/
theorem highRow_certificate_of_staged_dense_coefficients
    (block row : Nat)
    (hsupport : highRowSupport block row = true)
    (h0 : denseMRowNonnegative
      (highRowDenseCoefficientSlice block row 0 6) = true)
    (h1 : denseMRowNonnegative
      (highRowDenseCoefficientSlice block row 6 10) = true)
    (h2 : denseMRowNonnegative
      (highRowDenseCoefficientSlice block row 16 14) = true)
    (h3 : denseMRowNonnegative
      (highRowDenseCoefficientSlice block row 30 20) = true)
    (h4 : denseMRowNonnegative
      (highRowDenseCoefficientTail block row 50) = true) :
    ((highRowsBlockTail block row).take 1).all highRowPred = true := by
  apply highRow_certificate_of_support_and_dense block row hsupport
  exact highRowDenseCoefficientTail_nonnegative_of_slice block row 0 6 h0
    (highRowDenseCoefficientTail_nonnegative_of_slice block row 6 10 h1
      (highRowDenseCoefficientTail_nonnegative_of_slice block row 16 14 h2
        (highRowDenseCoefficientTail_nonnegative_of_slice block row 30 20 h3 h4)))

/-- The row certificate has its intended semantics: the cleared high-mode
numerator is nonnegative at every nonnegative pair `(M,Z)`. -/
theorem pExactLowerHigh_eval_nonnegative_of_rows
    (hcert : highRows.all highRowPred = true) (M Z : Q')
    (hM : (0 : Q') ≤ M) (hZ : (0 : Q') ≤ Z) :
    (0 : Q') ≤ RingNormaliser.eval (highEnvironment M Z) pExactLowerHigh := by
  have hrho : ∀ i, (0 : Q') ≤ highEnvironment M Z i := by
    intro i
    unfold highEnvironment
    by_cases hi0 : i = 0
    · rw [if_pos hi0]
      exact hM
    · rw [if_neg hi0]
      by_cases hi1 : i = 1
      · rw [if_pos hi1]
        exact hZ
      · rw [if_neg hi1]
        exact Q'.le_refl' 0
  have hrows : (0 : Q') ≤
      evalRows (highEnvironment M Z) Z (zRows pExactLowerHigh) :=
    evalRows_nonnegative (highEnvironment M Z) hrho Z hZ _
      (by simpa [highRows] using hcert)
  have hsem := evalRows_zRows (highEnvironment M Z) pExactLowerHigh
  have hsem' :
      evalRows (highEnvironment M Z) Z (zRows pExactLowerHigh) ≈
        RingNormaliser.eval (highEnvironment M Z) pExactLowerHigh := by
    simpa [highEnvironment] using hsem
  exact Q'.le_trans' _ _ _ hrows (Q'.le_of_eqv hsem')

#print axioms denseMRowNonnegative_append
#print axioms denseMRowNonnegative_of_take_and_drop
#print axioms highRowDenseCoefficientTail_nonnegative_of_slice
#print axioms highRow_certificate_of_support_and_dense
#print axioms highRow_certificate_of_staged_dense_coefficients
#print axioms pExactLowerHigh_rows_length
#print axioms pExactLowerHigh_eval_nonnegative_of_rows

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRows
