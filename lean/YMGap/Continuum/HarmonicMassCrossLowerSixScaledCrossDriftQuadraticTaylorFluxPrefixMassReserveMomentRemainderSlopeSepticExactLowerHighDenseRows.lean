/-
Dense bivariate coefficient semantics for the high-mode exact lower
polynomial.

The earlier row certificate retained each coefficient of the slack `Z` as a
general `PolyExpr` and then invoked the sparse normalizer independently.  The
actual polynomial is dense in only two variables.  Expanding directly into a
list of `Z` rows, each a dense list of `M` coefficients, avoids rebuilding the
same expression in every certificate module.  All operations below are
proved semantically over the constructive rationals.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRows

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighDenseRows

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

open YMGap.Constructive
open YMGap.Continuum.CoreBResidualSimplex
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRows

local infix:50 " ≈ " => Q'.eqv

abbrev PE := RingNormaliser.PolyExpr
abbrev DenseRow := List Int
abbrev DenseRows := List DenseRow

private def rowAdd : DenseRow → DenseRow → DenseRow
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: rowAdd p q

private def rowScale (a : Int) : DenseRow → DenseRow
  | [] => []
  | b :: q => (a * b) :: rowScale a q

private def rowShift : DenseRow → DenseRow
  | [] => []
  | q => 0 :: q

private def rowMul : DenseRow → DenseRow → DenseRow
  | [], _ => []
  | a :: p, q => rowAdd (rowScale a q) (rowShift (rowMul p q))

private def rowNeg : DenseRow → DenseRow
  | [] => []
  | a :: p => (-a) :: rowNeg p

private def rowsAdd : DenseRows → DenseRows → DenseRows
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => rowAdd a b :: rowsAdd p q

private def rowsScale (a : DenseRow) : DenseRows → DenseRows
  | [] => []
  | b :: q => rowMul a b :: rowsScale a q

private def rowsShift : DenseRows → DenseRows
  | [] => []
  | q => [] :: q

private def rowsMul : DenseRows → DenseRows → DenseRows
  | [], _ => []
  | a :: p, q => rowsAdd (rowsScale a q) (rowsShift (rowsMul p q))

private def rowsNeg : DenseRows → DenseRows
  | [] => []
  | a :: p => rowNeg a :: rowsNeg p

private def rowsPow (p : DenseRows) : Nat → DenseRows
  | 0 => [[1]]
  | n + 1 => rowsMul (rowsPow p n) p

/-- Dense bivariate expansion.  An inner list is ordered by increasing power
of variable zero (`M`); the outer list is ordered by increasing power of
variable one (`Z`).  Variables beyond one evaluate to zero in the intended
environment and therefore have zero dense expansion. -/
def denseRows : PE → DenseRows
  | .const c => [[c]]
  | .var i => if i = 0 then [[0, 1]] else if i = 1 then [[], [1]] else [[]]
  | .add a b => rowsAdd (denseRows a) (denseRows b)
  | .mul a b => rowsMul (denseRows a) (denseRows b)
  | .neg a => rowsNeg (denseRows a)
  | .pow a n => rowsPow (denseRows a) n

def denseRowNonnegative : DenseRow → Bool
  | [] => true
  | a :: p => decide ((0 : Int) ≤ a) && denseRowNonnegative p

def denseRowsNonnegative (e : PE) : Bool :=
  (denseRows e).all denseRowNonnegative

private def evalRow (M : Q') : DenseRow → Q'
  | [] => 0
  | a :: p => Q'.ofInt a + M * evalRow M p

private def evalRows (M Z : Q') : DenseRows → Q'
  | [] => 0
  | a :: p => evalRow M a + Z * evalRows M Z p

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

private theorem ofInt_neg (a : Int) : Q'.ofInt (-a) ≈ -(Q'.ofInt a) := by
  show (-a) * (1 : Int) = (-a) * (1 : Int)
  rfl

private theorem evalRow_add (M : Q') : ∀ p q,
    evalRow M (rowAdd p q) ≈ evalRow M p + evalRow M q
  | [], q => Q'.eqv_symm (RingNormaliser.eqv_of_eq (Q'.zero_add' _))
  | _ :: _, [] => Q'.eqv_symm (RingNormaliser.eqv_of_eq (Q'.add_zero' _))
  | a :: p, b :: q => by
      refine Q'.eqv_trans _
        ((Q'.ofInt a + Q'.ofInt b) +
          M * (evalRow M p + evalRow M q)) _ ?_ ?_
      · exact add_congr₂ (RingNormaliser.ofInt_add a b)
          (Q'.mul_eqv_congr_left M _ _ (evalRow_add M p q))
      refine Q'.eqv_trans _
        ((Q'.ofInt a + Q'.ofInt b) +
          (M * evalRow M p + M * evalRow M q)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.mul_add_eqv M (evalRow M p) (evalRow M q))
      exact Q'.add_swap_inner _ _ _ _

private theorem evalRow_scale (M : Q') (a : Int) : ∀ p,
    evalRow M (rowScale a p) ≈ Q'.ofInt a * evalRow M p
  | [] => Q'.eqv_symm (mul_zero_eqv _)
  | b :: p => by
      refine Q'.eqv_trans _
        (Q'.ofInt a * Q'.ofInt b +
          M * (Q'.ofInt a * evalRow M p)) _ ?_ ?_
      · exact add_congr₂ (RingNormaliser.ofInt_mul a b)
          (Q'.mul_eqv_congr_left M _ _ (evalRow_scale M a p))
      refine Q'.eqv_trans _
        (Q'.ofInt a * Q'.ofInt b +
          Q'.ofInt a * (M * evalRow M p)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (mul_swap_first M (Q'.ofInt a) (evalRow M p))
      exact Q'.eqv_symm (Q'.mul_add_eqv _ _ _)

private theorem evalRow_shift (M : Q') : ∀ p,
    evalRow M (rowShift p) ≈ M * evalRow M p
  | [] => Q'.eqv_symm (mul_zero_eqv M)
  | _ :: _ => RingNormaliser.eqv_of_eq (Q'.zero_add' _)

private theorem evalRow_mul (M : Q') : ∀ p q,
    evalRow M (rowMul p q) ≈ evalRow M p * evalRow M q
  | [], q => Q'.eqv_symm (RingNormaliser.q_zero_mul (evalRow M q))
  | a :: p, q => by
      refine Q'.eqv_trans _
        (evalRow M (rowScale a q) + evalRow M (rowShift (rowMul p q))) _
        (evalRow_add M _ _) ?_
      refine Q'.eqv_trans _
        (Q'.ofInt a * evalRow M q + M * evalRow M (rowMul p q)) _ ?_ ?_
      · exact add_congr₂ (evalRow_scale M a q) (evalRow_shift M (rowMul p q))
      refine Q'.eqv_trans _
        (Q'.ofInt a * evalRow M q + M * (evalRow M p * evalRow M q)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left M _ _ (evalRow_mul M p q))
      refine Q'.eqv_trans _
        (Q'.ofInt a * evalRow M q + (M * evalRow M p) * evalRow M q) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv M (evalRow M p) (evalRow M q)))
      exact Q'.eqv_symm (RingNormaliser.q_add_mul _ _ _)

private theorem evalRow_neg (M : Q') : ∀ p,
    evalRow M (rowNeg p) ≈ -(evalRow M p)
  | [] => RingNormaliser.eqv_of_eq rfl
  | a :: p => by
      refine Q'.eqv_trans _
        (-(Q'.ofInt a) + M * (-(evalRow M p))) _ ?_ ?_
      · exact add_congr₂ (ofInt_neg a)
          (Q'.mul_eqv_congr_left M _ _ (evalRow_neg M p))
      refine Q'.eqv_trans _
        (-(Q'.ofInt a) + -(M * evalRow M p)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv M (evalRow M p))
      exact Q'.eqv_symm (Q'.neg_add_eqv_split (Q'.ofInt a) (M * evalRow M p))

private theorem evalRows_add (M Z : Q') : ∀ p q,
    evalRows M Z (rowsAdd p q) ≈ evalRows M Z p + evalRows M Z q
  | [], q => Q'.eqv_symm (RingNormaliser.eqv_of_eq (Q'.zero_add' _))
  | _ :: _, [] => Q'.eqv_symm (RingNormaliser.eqv_of_eq (Q'.add_zero' _))
  | a :: p, b :: q => by
      refine Q'.eqv_trans _
        ((evalRow M a + evalRow M b) +
          Z * (evalRows M Z p + evalRows M Z q)) _ ?_ ?_
      · exact add_congr₂ (evalRow_add M a b)
          (Q'.mul_eqv_congr_left Z _ _ (evalRows_add M Z p q))
      refine Q'.eqv_trans _
        ((evalRow M a + evalRow M b) +
          (Z * evalRows M Z p + Z * evalRows M Z q)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.mul_add_eqv Z (evalRows M Z p) (evalRows M Z q))
      exact Q'.add_swap_inner _ _ _ _

private theorem evalRows_scale (M Z : Q') (a : DenseRow) : ∀ p,
    evalRows M Z (rowsScale a p) ≈ evalRow M a * evalRows M Z p
  | [] => Q'.eqv_symm (mul_zero_eqv _)
  | b :: p => by
      refine Q'.eqv_trans _
        (evalRow M a * evalRow M b +
          Z * (evalRow M a * evalRows M Z p)) _ ?_ ?_
      · exact add_congr₂ (evalRow_mul M a b)
          (Q'.mul_eqv_congr_left Z _ _ (evalRows_scale M Z a p))
      refine Q'.eqv_trans _
        (evalRow M a * evalRow M b +
          evalRow M a * (Z * evalRows M Z p)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (mul_swap_first Z (evalRow M a) (evalRows M Z p))
      exact Q'.eqv_symm (Q'.mul_add_eqv _ _ _)

private theorem evalRows_shift (M Z : Q') : ∀ p,
    evalRows M Z (rowsShift p) ≈ Z * evalRows M Z p
  | [] => Q'.eqv_symm (mul_zero_eqv Z)
  | _ :: _ => RingNormaliser.eqv_of_eq (Q'.zero_add' _)

private theorem evalRows_mul (M Z : Q') : ∀ p q,
    evalRows M Z (rowsMul p q) ≈ evalRows M Z p * evalRows M Z q
  | [], q => Q'.eqv_symm (RingNormaliser.q_zero_mul (evalRows M Z q))
  | a :: p, q => by
      refine Q'.eqv_trans _
        (evalRows M Z (rowsScale a q) + evalRows M Z (rowsShift (rowsMul p q))) _
        (evalRows_add M Z _ _) ?_
      refine Q'.eqv_trans _
        (evalRow M a * evalRows M Z q + Z * evalRows M Z (rowsMul p q)) _ ?_ ?_
      · exact add_congr₂ (evalRows_scale M Z a q)
          (evalRows_shift M Z (rowsMul p q))
      refine Q'.eqv_trans _
        (evalRow M a * evalRows M Z q +
          Z * (evalRows M Z p * evalRows M Z q)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left Z _ _ (evalRows_mul M Z p q))
      refine Q'.eqv_trans _
        (evalRow M a * evalRows M Z q +
          (Z * evalRows M Z p) * evalRows M Z q) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv Z (evalRows M Z p) (evalRows M Z q)))
      exact Q'.eqv_symm (RingNormaliser.q_add_mul _ _ _)

private theorem evalRows_neg (M Z : Q') : ∀ p,
    evalRows M Z (rowsNeg p) ≈ -(evalRows M Z p)
  | [] => RingNormaliser.eqv_of_eq rfl
  | a :: p => by
      refine Q'.eqv_trans _
        (-(evalRow M a) + Z * (-(evalRows M Z p))) _ ?_ ?_
      · exact add_congr₂ (evalRow_neg M a)
          (Q'.mul_eqv_congr_left Z _ _ (evalRows_neg M Z p))
      refine Q'.eqv_trans _
        (-(evalRow M a) + -(Z * evalRows M Z p)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv Z (evalRows M Z p))
      exact Q'.eqv_symm (Q'.neg_add_eqv_split (evalRow M a) (Z * evalRows M Z p))

private theorem evalRows_pow (M Z : Q') (p : DenseRows) : ∀ n,
    evalRows M Z (rowsPow p n) ≈ RingNormaliser.qpow (evalRows M Z p) n
  | 0 => by
      refine Q'.eqv_trans _ (((1 : Q') + 0) + 0) _ ?_ ?_
      · exact add_congr₂
          (Q'.add_eqv_congr_left 1 _ 0 (mul_zero_eqv M))
          (mul_zero_eqv Z)
      rw [Q'.add_zero' 1, Q'.add_zero' 1]
      exact Q'.eqv_refl 1
  | n + 1 => by
      refine Q'.eqv_trans _
        (evalRows M Z (rowsPow p n) * evalRows M Z p) _
        (evalRows_mul M Z _ _) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (evalRows_pow M Z p n)

private theorem dense_var_zero_value (M Z : Q') :
    (0 + M * (1 + M * 0) + Z * 0) ≈ M := by
  refine Q'.eqv_trans _ (0 + M * (1 + 0) + 0) _ ?_ ?_
  · exact add_congr₂
      (Q'.add_eqv_congr_left 0 _ _
        (Q'.mul_eqv_congr_left M _ _
          (Q'.add_eqv_congr_left 1 _ 0 (mul_zero_eqv M))))
      (mul_zero_eqv Z)
  rw [Q'.add_zero' 1]
  refine Q'.eqv_trans _ (0 + M + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ 0
      (Q'.add_eqv_congr_left 0 _ _ (Q'.mul_one_eqv M))
  rw [Q'.zero_add' M, Q'.add_zero' M]
  exact Q'.eqv_refl M

private theorem dense_const_value (M Z : Q') (c : Int) :
    (Q'.ofInt c + M * 0 + Z * 0) ≈ Q'.ofInt c := by
  refine Q'.eqv_trans _ (Q'.ofInt c + 0 + 0) _ ?_ ?_
  · exact add_congr₂
      (Q'.add_eqv_congr_left (Q'.ofInt c) _ 0 (mul_zero_eqv M))
      (mul_zero_eqv Z)
  rw [Q'.add_zero' (Q'.ofInt c), Q'.add_zero' (Q'.ofInt c)]
  exact Q'.eqv_refl (Q'.ofInt c)

private theorem dense_var_one_value (M Z : Q') :
    (0 + Z * (1 + M * 0 + Z * 0)) ≈ Z := by
  refine Q'.eqv_trans _ (0 + Z * (1 + 0 + 0)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left 0 _ _
      (Q'.mul_eqv_congr_left Z _ _
        (add_congr₂
          (Q'.add_eqv_congr_left 1 _ 0 (mul_zero_eqv M))
          (mul_zero_eqv Z)))
  rw [Q'.add_zero' 1, Q'.add_zero' 1]
  refine Q'.eqv_trans _ (0 + Z) _ ?_ ?_
  · exact Q'.add_eqv_congr_left 0 _ _ (Q'.mul_one_eqv Z)
  exact RingNormaliser.eqv_of_eq (Q'.zero_add' Z)

private theorem dense_var_other_value (Z : Q') : (0 + Z * 0) ≈ 0 := by
  refine Q'.eqv_trans _ (0 + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr_left 0 _ 0 (mul_zero_eqv Z)
  exact RingNormaliser.eqv_of_eq (Q'.zero_add' 0)

private theorem evalRows_denseRows_var_fast (M Z : Q') (i : Nat) :
    evalRows M Z (denseRows (.var i)) ≈
      RingNormaliser.eval (highEnvironment M Z) (.var i) := by
  cases i with
  | zero =>
      have h00 : (0 : Nat) = 0 := rfl
      simpa only [denseRows, if_pos h00, evalRows, evalRow, highEnvironment,
        RingNormaliser.eval, RingNormaliser.ofInt_zero,
        RingNormaliser.ofInt_one] using dense_var_zero_value M Z
  | succ i =>
      cases i with
      | zero =>
          have h10 : (1 : Nat) ≠ 0 := by decide
          have h11 : (1 : Nat) = 1 := rfl
          simpa only [denseRows, if_neg h10, if_pos h11, evalRows, evalRow,
            highEnvironment, RingNormaliser.eval, RingNormaliser.ofInt_one]
            using dense_var_one_value M Z
      | succ i =>
          have h0 : Nat.succ (Nat.succ i) ≠ 0 := Nat.succ_ne_zero _
          have h1 : Nat.succ (Nat.succ i) ≠ 1 := by
            intro h
            have hs : Nat.succ i = 0 := Nat.succ.inj h
            exact Nat.succ_ne_zero i hs
          simpa only [denseRows, if_neg h0, if_neg h1, evalRows, evalRow,
            highEnvironment, RingNormaliser.eval] using dense_var_other_value Z

private theorem evalRows_denseRows_fast (M Z : Q') : ∀ e,
    evalRows M Z (denseRows e) ≈
      RingNormaliser.eval (highEnvironment M Z) e
  | .const c => by
      simpa [denseRows, evalRows, evalRow, RingNormaliser.eval] using
        dense_const_value M Z c
  | .var i => evalRows_denseRows_var_fast M Z i
  | .add a b => by
      refine Q'.eqv_trans _
        (evalRows M Z (denseRows a) + evalRows M Z (denseRows b)) _
        (evalRows_add M Z _ _) ?_
      exact add_congr₂ (evalRows_denseRows_fast M Z a)
        (evalRows_denseRows_fast M Z b)
  | .mul a b => by
      refine Q'.eqv_trans _
        (evalRows M Z (denseRows a) * evalRows M Z (denseRows b)) _
        (evalRows_mul M Z _ _) ?_
      exact mul_congr₂ (evalRows_denseRows_fast M Z a)
        (evalRows_denseRows_fast M Z b)
  | .neg a => by
      refine Q'.eqv_trans _ (-(evalRows M Z (denseRows a))) _
        (evalRows_neg M Z _) ?_
      exact Q'.neg_eqv_congr _ _ (evalRows_denseRows_fast M Z a)
  | .pow a n => by
      refine Q'.eqv_trans _
        (RingNormaliser.qpow (evalRows M Z (denseRows a)) n) _
        (evalRows_pow M Z _ n) ?_
      exact RingNormaliser.qpow_eqv_congr (evalRows_denseRows_fast M Z a) n

private theorem ofInt_nonnegative {a : Int} (ha : (0 : Int) ≤ a) :
    (0 : Q') ≤ Q'.ofInt a := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact ha

private theorem evalRow_nonnegative (M : Q') (hM : (0 : Q') ≤ M) :
    ∀ p, denseRowNonnegative p = true → (0 : Q') ≤ evalRow M p
  | [], _ => Q'.le_refl' 0
  | a :: p, hp => by
      have hs : decide ((0 : Int) ≤ a) = true ∧ denseRowNonnegative p = true := by
        simpa [denseRowNonnegative] using hp
      exact Q'.zero_le_add _ _
        (ofInt_nonnegative (of_decide_eq_true hs.1))
        (Q'.mul_nonneg _ _ hM (evalRow_nonnegative M hM p hs.2))

private theorem evalRows_nonnegative (M Z : Q')
    (hM : (0 : Q') ≤ M) (hZ : (0 : Q') ≤ Z) :
    ∀ p, p.all denseRowNonnegative = true → (0 : Q') ≤ evalRows M Z p
  | [], _ => Q'.le_refl' 0
  | a :: p, hp => by
      have hs : denseRowNonnegative a = true ∧ p.all denseRowNonnegative = true := by
        simpa using hp
      exact Q'.zero_le_add _ _
        (evalRow_nonnegative M hM a hs.1)
        (Q'.mul_nonneg _ _ hZ (evalRows_nonnegative M Z hM hZ p hs.2))

/-- A dense coefficient certificate has its intended pointwise semantics. -/
theorem eval_nonnegative_of_dense_rows {e : PE}
    (hcert : denseRowsNonnegative e = true)
    (M Z : Q') (hM : (0 : Q') ≤ M) (hZ : (0 : Q') ≤ Z) :
    (0 : Q') ≤ RingNormaliser.eval (highEnvironment M Z) e := by
  change (denseRows e).all denseRowNonnegative = true at hcert
  have hrows : (0 : Q') ≤ evalRows M Z (denseRows e) :=
    evalRows_nonnegative M Z hM hZ _ hcert
  exact Q'.le_trans' _ _ _ hrows
    (Q'.le_of_eqv (evalRows_denseRows_fast M Z e))

#print axioms eval_nonnegative_of_dense_rows

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighDenseRows
