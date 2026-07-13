/-
`HarmonicCutoffBoundary` — the physical harmonic weight and quadratic
character cutoff suppress the terminal character coefficient by one harmonic
factor.

With `m=k+2`, `u_k=1/m`, `w_k=1-u_k`, and `N_k=m^2`, reciprocal Bernoulli gives

  w_k^c4(N_k) (1+c4(N_k)u_k) <= 1.

The exact arithmetic inequality

  dim(N_k) <= u_k (1+c4(N_k)u_k)

then yields `coeffW w_k N_k <= u_k`.  Squaring gives the inverse-square
boundary envelope required by the Dirichlet identity, together with the
existing explicit inverse-square window modulus.
-/

import YMGap.Continuum.ReciprocalBernoulliUpper
import YMGap.Continuum.QuadraticCutoffSchedule
import YMGap.Continuum.BondMovingStep
import YMGap.Continuum.BakryEmery

namespace YMGap.Continuum.HarmonicCutoffBoundary

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

/-- Physical harmonic margin `u_k=1/(k+2)`. -/
def harmU (k : Nat) : Q' := unit (k + 2) (by omega)

/-- Physical harmonic weight `w_k=1-u_k`. -/
def harmW (k : Nat) : Q' := oneSub (harmU k)

theorem harmU_pos (k : Nat) : (0 : Q') < harmU k := unit_pos _ _
theorem harmU_nonneg (k : Nat) : (0 : Q') ≤ harmU k := unit_nonneg _ _

theorem harmU_le_one (k : Nat) : harmU k ≤ (1 : Q') := by
  exact unit_antitone (by decide) (by omega) (by omega : 1 ≤ k + 2)

theorem harmW_nonneg (k : Nat) : (0 : Q') ≤ harmW k := by
  unfold harmW oneSub
  exact Q'.sub_nonneg_of_le (harmU_le_one k)

theorem harmW_le_one (k : Nat) : harmW k ≤ (1 : Q') := by
  unfold harmW oneSub
  have hneg0 : -harmU k ≤ -(0 : Q') := Q'.neg_le_neg (harmU_nonneg k)
  have hneg : -harmU k ≤ (0 : Q') :=
    Q'.le_trans' _ _ _ hneg0
      (Q'.le_of_eqv (by decide : (-(0 : Q')).eqv 0))
  have hadd := Q'.add_le_add_left (1 : Q') (-harmU k) 0 hneg
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1)))

private theorem nat_cleared_bound (k : Nat) :
    (Ncut k + 1) * ((k + 2) * (k + 2)) ≤
      (k + 2) + c4 (Ncut k) := by
  unfold Ncut c4
  simp only [Nat.add_mul, Nat.mul_add]
  omega

/-- Cleared dimension-vs-Bernoulli-denominator arithmetic. -/
theorem dim_le_margin_mul_bernDen (k : Nat) :
    dimQ (Ncut k) ≤ harmU k * bernDen (harmU k) (c4 (Ncut k)) := by
  show (dimQ (Ncut k)).num *
      ((harmU k * bernDen (harmU k) (c4 (Ncut k))).den : Int) ≤
    (harmU k * bernDen (harmU k) (c4 (Ncut k))).num *
      (dimQ (Ncut k)).den
  unfold harmU unit bernDen dimQ
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Q'.mul_num_cast, Q'.mul_den_cast, Q'.add_num_cast, Q'.add_den_cast,
    Q'.mkPos_num, Q'.mkPos_den, Int.mul_one, Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.one_mul, Int.mul_one]
  push_cast
  exact_mod_cast nat_cleared_bound k

/-- **Terminal-character harmonic bound.** -/
theorem coeffW_Ncut_le_harmU (k : Nat) :
    coeffW (harmW k) (Ncut k) ≤ harmU k := by
  let u := harmU k
  let n := c4 (Ncut k)
  let D := bernDen u n
  have hbern := oneSub_pow_mul_bernDen_le (harmU_nonneg k) (harmU_le_one k) n
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ (dimQ (Ncut k)) hbern
    (dimQ_nonneg (Ncut k))
  have hleft : dimQ (Ncut k) * (qpow (harmW k) n * D) ≈
      coeffW (harmW k) (Ncut k) * D := by
    dsimp only [n, D]
    unfold coeffW
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv (dimQ (Ncut k))
        (qpow (harmW k) (c4 (Ncut k)))
        (bernDen (harmU k) (c4 (Ncut k))))
  have hright : dimQ (Ncut k) * (1 : Q') ≈ dimQ (Ncut k) :=
    Q'.mul_one_eqv _
  have hcleared : coeffW (harmW k) (Ncut k) * D ≤ harmU k * D := by
    have h1 : coeffW (harmW k) (Ncut k) * D ≤ dimQ (Ncut k) :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
        (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hright))
    exact Q'.le_trans' _ _ _ h1 (dim_le_margin_mul_bernDen k)
  exact BakryEmery.le_of_mul_le_mul_right_pos
    (bernDen_pos (harmU_nonneg k) n) hcleared

/-- The terminal boundary square is inverse-square dominated. -/
theorem coeffW_Ncut_sq_le_invSq (k : Nat) :
    coeffW (harmW k) (Ncut k) * coeffW (harmW k) (Ncut k) ≤
      invSqTerm 2 (by decide) k := by
  have hsq := Q'.mul_le_mul_of_nonneg
    (coeffW_Ncut_le_harmU k) (coeffW_Ncut_le_harmU k)
    (harmU_nonneg k) (coeffW_nonneg (harmW_nonneg k) (Ncut k))
  refine Q'.le_trans' _ _ _ hsq ?_
  exact Q'.le_of_eqv (by
    have hm : 0 < k + 2 := by omega
    have hmm : 0 < (k + 2) * (k + 2) := Nat.mul_pos hm hm
    unfold harmU unit invSqTerm
    show (Q'.mkPos 1 (k + 2) hm *
        Q'.mkPos 1 (k + 2) hm).num *
        ((Q'.mkPos 1 ((k + 2) * (k + 2)) hmm).den : Int) =
      (Q'.mkPos 1 ((k + 2) * (k + 2)) hmm).num *
        ((Q'.mkPos 1 (k + 2) hm *
          Q'.mkPos 1 (k + 2) hm).den : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast,
      Q'.mkPos_num, Q'.mkPos_den]
    push_cast
    omega)

/-- Explicit inverse-square window modulus for the actual boundary square. -/
theorem boundarySq_window_modulus (N M : Nat) :
    tailSum
        (fun k => coeffW (harmW k) (Ncut k) * coeffW (harmW k) (Ncut k))
        N M ≤ pot 2 (by decide) N := by
  have h := summableBound_of_invSq 2 (by decide) (1 : Q') (by decide)
      (fun k => coeffW (harmW k) (Ncut k) * coeffW (harmW k) (Ncut k))
      (fun k => Q'.le_trans' _ _ _ (coeffW_Ncut_sq_le_invSq k)
        (Q'.ge_of_eqv (Q'.one_mul_eqv _))) N M
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv _))

end YMGap.Continuum.HarmonicCutoffBoundary

#print axioms YMGap.Continuum.HarmonicCutoffBoundary.dim_le_margin_mul_bernDen
#print axioms YMGap.Continuum.HarmonicCutoffBoundary.coeffW_Ncut_le_harmU
#print axioms YMGap.Continuum.HarmonicCutoffBoundary.coeffW_Ncut_sq_le_invSq
#print axioms YMGap.Continuum.HarmonicCutoffBoundary.boundarySq_window_modulus
