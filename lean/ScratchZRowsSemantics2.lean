import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate

namespace ScratchZRowsSemantics2

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CoreBResidualSimplex
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := RingNormaliser.PolyExpr

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

private def zRows : PE → List PE
  | .const c => [.const c]
  | .var i => if i = 1 then [.const 0, .const 1] else [.var i]
  | .add a b => zAdd (zRows a) (zRows b)
  | .mul a b => zMul (zRows a) (zRows b)
  | .neg a => zNeg (zRows a)
  | .pow a n => zPow (zRows a) n

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
      rows.all (fun row =>
        RawCoefficientsNonnegative (fastNormalize row)) = true →
      (0 : Q') ≤ evalRows rho z rows
  | [], _ => Q'.le_refl' 0
  | row :: rows, hrows => by
      have hs :
          RawCoefficientsNonnegative (fastNormalize row) = true ∧
          rows.all (fun r =>
            RawCoefficientsNonnegative (fastNormalize r)) = true := by
        simpa using hrows
      exact Q'.zero_le_add _ _
        (eval_nonneg_of_fast_coefficients hrho hs.1)
        (Q'.mul_nonneg _ _ hz
          (evalRows_nonnegative rho hrho z hz rows hs.2))

#print axioms evalRows_zRows
#print axioms evalRows_nonnegative

end ScratchZRowsSemantics2
